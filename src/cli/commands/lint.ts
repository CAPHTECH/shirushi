/**
 * Lint Command
 *
 * ドキュメントとインデックスの整合性を検証する。
 * 終了コード: 0 (成功) / 1 (エラーあり)
 *
 * オプション:
 * - --format <table|json>: 出力フォーマット
 * - --quiet: エラーパスのみ出力
 * - --base <ref>: Git参照との差分でdoc_id変更を検出
 * - --changed-only: 変更ファイルのみをlint
 */

import { isLeft, isRight } from 'fp-ts/Either';
import { minimatch } from 'minimatch';

import { loadConfigForCommand } from '@/cli/helpers/config';
import {
  buildLintResult,
  formatLintResult,
  problemToLintError,
  validationErrorToLintError,
  formatLintQuiet,
} from '@/cli/output/reporters';
import {
  loadIndexFile,
  validateIndexConsistency,
} from '@/core/index-manager';
import { scanDocuments } from '@/core/scanner';
import { validateDocId } from '@/core/validator';
import { ShirushiErrors, LawDomain, ErrorSeverity } from '@/errors/definitions';
import {
  createGitOperations,
  createChangeDetector,
} from '@/git';
import { logger } from '@/utils/logger';

import type { OutputFormat } from '@/cli/output/formatters';
import type { LintError } from '@/cli/output/reporters';
import type { ShirushiConfig } from '@/config/schema';
import type { ScanResult } from '@/core/scanner';
import type { GitError, ChangeDetectionResult, ChangedFile, DetectionTarget } from '@/git';
import type { Command } from 'commander';

/**
 * lintコマンドオプション
 */
export interface LintOptions {
  config?: string;
  format?: OutputFormat;
  quiet?: boolean;
  /** ベースディレクトリ（テスト用、デフォルト: process.cwd()） */
  cwd?: string;
  /** Git参照（ブランチ、タグ、コミット）との差分でdoc_id変更を検出 */
  base?: string;
  /** 変更ファイルのみをlint */
  changedOnly?: boolean;
}

/**
 * Commander.jsアクションハンドラ用の型定義
 */
interface LintCliOptions {
  config?: string;
  format?: string;
  quiet?: boolean;
  base?: string;
  changedOnly?: boolean;
}

/**
 * GitErrorをフォーマット
 */
function formatGitError(error: GitError): string {
  let msg = `Error: ${error.message}`;
  if (error.context?.ref) {
    msg += `\n  Reference: ${error.context.ref}`;
  }
  if (error.context?.path) {
    msg += `\n  Path: ${error.context.path}`;
  }
  return msg;
}

/**
 * パスを正規化（バックスラッシュをフォワードスラッシュに変換）
 * Windows互換性のため
 */
function normalizePath(filePath: string): string {
  return filePath.replace(/\\/g, '/');
}

/**
 * ファイルパスがdoc_globsにマッチするかチェック
 * Windows互換性のためパスを正規化してからマッチング
 */
function matchesDocGlobs(filePath: string, globs: string[]): boolean {
  const normalizedPath = normalizePath(filePath);
  return globs.some((pattern) => minimatch(normalizedPath, pattern));
}

/**
 * 変更検出結果をLintErrorに変換
 *
 * doc_id変更と、検出中に発生したGitエラーの両方をLintErrorに変換する。
 * 個別ファイルのGitエラー（git show失敗など）を無視すると、
 * doc_id改ざんが見落とされる可能性があるため、エラーとして報告する。
 */
function changeResultToLintErrors(
  result: ChangeDetectionResult,
  baseRef: string
): LintError[] {
  const errors: LintError[] = [];

  // doc_id変更をエラーに変換
  for (const change of result.changedDocIds) {
    errors.push({
      path: change.path,
      code: ShirushiErrors.DOC_ID_CHANGED.code,
      message: `doc_id changed from "${change.oldDocId ?? '(none)'}" to "${change.newDocId ?? '(none)'}" (base: ${baseRef})`,
      domain: LawDomain.Git,
      severity: ErrorSeverity.Error,
      details: {
        oldDocId: change.oldDocId,
        newDocId: change.newDocId,
        baseRef,
      },
    });
  }

  // 検出中に発生したGitエラーもLintErrorとして報告
  // これにより、git show失敗などで検出できなかったファイルが明示される
  for (const gitError of result.errors) {
    errors.push({
      path: gitError.context?.path ?? '(unknown)',
      code: gitError.code,
      message: gitError.message,
      domain: LawDomain.Git,
      severity: ErrorSeverity.Error,
      details: {
        baseRef,
        originalError: gitError.context?.originalError,
      },
    });
  }

  return errors;
}

/**
 * ドキュメントの問題を収集する
 */
function collectDocumentIssues(
  scanResult: ScanResult,
  config: ShirushiConfig
): LintError[] {
  const issues: LintError[] = [];

  for (const doc of scanResult.documents) {
    // パース時の問題を追加
    for (const problem of doc.problems) {
      issues.push(problemToLintError(doc.path, problem));
    }

    // doc_idがあれば検証
    if (doc.docId) {
      const validationResult = validateDocId(
        {
          docId: doc.docId,
          documentPath: doc.path,
          documentMeta: doc.metadata,
        },
        config
      );

      if (!validationResult.valid) {
        for (const error of validationResult.errors) {
          issues.push(validationErrorToLintError(doc.path, error));
        }
      }
    }
  }

  return issues;
}

/**
 * インデックス整合性を検証する
 */
async function validateIndex(
  scanResult: ScanResult,
  indexFilePath: string,
  cwd: string,
  idField: string = 'doc_id'
): Promise<LintError[]> {
  try {
    const indexFile = await loadIndexFile(indexFilePath, cwd, idField);
    const indexResult = validateIndexConsistency(
      scanResult.documents,
      indexFile,
      cwd,
      idField
    );
    return indexResult.errors;
  } catch (error) {
    const message =
      error instanceof Error ? error.message : 'Unknown index error';
    console.error(`Error loading index: ${message}`);
    logger.warn('lint.index', 'Failed to load index file', { error: message });
    return [];
  }
}

/**
 * Git環境を検証
 */
async function validateGitEnvironment(
  cwd: string,
  baseRef?: string
): Promise<GitError | null> {
  const gitOps = createGitOperations({ cwd });

  // Gitリポジトリかチェック
  const isRepoResult = await gitOps.isGitRepository();
  if (isLeft(isRepoResult)) {
    return isRepoResult.left;
  }
  if (!isRepoResult.right) {
    return {
      code: 'NOT_A_GIT_REPO',
      message: ShirushiErrors.NOT_A_GIT_REPO.message,
    };
  }

  // baseRefが指定されていれば有効性をチェック
  if (baseRef) {
    const isValidResult = await gitOps.isValidRef(baseRef);
    if (isLeft(isValidResult)) {
      return isValidResult.left;
    }
    if (!isValidResult.right) {
      return {
        code: 'INVALID_GIT_REF',
        message: `${ShirushiErrors.INVALID_GIT_REF.message}: ${baseRef}`,
        context: { ref: baseRef },
      };
    }
  }

  return null;
}

/**
 * lintコマンドを実行
 */
export async function executeLint(options: LintOptions): Promise<number> {
  const cwd = options.cwd ?? process.cwd();
  const format = options.format ?? 'table';

  logger.debug('lint.start', 'Starting lint command', { options });

  // 1. Git環境検証（--base または --changed-only 指定時）
  if (options.base || options.changedOnly) {
    const gitError = await validateGitEnvironment(cwd, options.base);
    if (gitError) {
      console.error(formatGitError(gitError));
      return 1;
    }
  }

  // 2. 設定を読み込み
  const loaded = await loadConfigForCommand(options.config, cwd, 'lint');
  if (!loaded) {
    return 1;
  }
  const { config } = loaded;

  // 3. 変更ファイルを取得（--changed-only 指定時、または --base 指定時）
  // リネーム情報を保持するためにChangedFile[]を保存
  let changedFiles: ChangedFile[] | undefined;
  let targetPaths: string[] | undefined;

  if (options.changedOnly || options.base) {
    const gitOps = createGitOperations({ cwd });
    const changedResult = await gitOps.getChangedFiles(options.base);

    if (isLeft(changedResult)) {
      console.error(formatGitError(changedResult.left));
      return 1;
    }

    changedFiles = changedResult.right;
  }

  if (options.changedOnly && changedFiles) {
    // 削除ファイルを除外し、doc_globsにマッチするファイルのみ
    // Windows互換性のためパスを正規化
    targetPaths = changedFiles
      .filter((f) => f.status !== 'deleted')
      .filter((f) => matchesDocGlobs(f.path, config.doc_globs))
      .map((f) => normalizePath(f.path));

    if (targetPaths.length === 0) {
      if (!options.quiet) {
        console.log('No changed documents to lint.');
      }
      return 0;
    }

    logger.debug('lint.changed', 'Linting changed files only', {
      count: targetPaths.length,
    });
  }

  // 4. ドキュメントをスキャン
  const scanResult = await scanDocuments(config, {
    cwd,
    ...(targetPaths ? { filterPaths: targetPaths } : {}),
  });
  logger.debug('lint.scan', 'Documents scanned', {
    count: scanResult.documents.length,
  });

  // 5. 問題を収集
  const documentIssues = collectDocumentIssues(scanResult, config);

  // 6. インデックス整合性を検証
  const idField = config.id_field ?? 'doc_id';
  const indexIssues = await validateIndex(scanResult, config.index_file, cwd, idField);

  // 7. Git差分でdoc_id変更を検出（--base 指定時 かつ forbid_id_change が true）
  let gitIssues: LintError[] = [];
  if (options.base && config.forbid_id_change) {
    const gitOps = createGitOperations({ cwd });
    const detector = createChangeDetector(gitOps, idField);

    // リネーム情報を含む検出対象を構築
    // changedFilesからリネーム情報を取得し、スキャンされたドキュメントと紐付ける
    const detectionTargets: DetectionTarget[] = scanResult.documents.map((d) => {
      // changedFilesからこのパスに対応するエントリを検索
      // Windows互換性のためパスを正規化して比較
      const normalizedDocPath = normalizePath(d.path);
      const changedFile = changedFiles?.find(
        (f) => normalizePath(f.path) === normalizedDocPath
      );
      return {
        path: d.path,
        // リネームされたファイルの場合、oldPathを設定
        // これにより、baseRefでは旧パスからコンテンツを取得する
        ...(changedFile?.oldPath ? { oldPath: changedFile.oldPath } : {}),
      };
    });

    const changeResult = await detector.detectDocIdChanges(
      options.base,
      detectionTargets
    );

    if (isRight(changeResult)) {
      gitIssues = changeResultToLintErrors(changeResult.right, options.base);
    } else {
      console.error(formatGitError(changeResult.left));
      return 1;
    }
  }

  // 8. 結果を構築
  const allIssues = [...documentIssues, ...indexIssues, ...gitIssues];
  const result = buildLintResult(allIssues);

  // 9. 出力
  if (options.quiet) {
    const output = formatLintQuiet(result);
    if (output) {
      console.log(output);
    }
  } else {
    console.log(formatLintResult(result, format));
  }

  // 10. 終了コード
  return result.summary.totalErrors > 0 ? 1 : 0;
}

/**
 * Commanderにlintコマンドを登録
 */
export function registerLintCommand(program: Command): void {
  program
    .command('lint')
    .description('Validate document IDs and index consistency')
    .option('-c, --config <path>', 'Path to config file')
    .option(
      '-f, --format <format>',
      'Output format (table, json)',
      'table'
    )
    .option('-q, --quiet', 'Quiet mode (only show file paths with errors)')
    .option(
      '-b, --base <ref>',
      'Git reference to compare against (branch, tag, or commit)'
    )
    .option('--changed-only', 'Only lint files that have been modified')
    .action(async (opts: LintCliOptions) => {
      const exitCode = await executeLint({
        ...(opts.config ? { config: opts.config } : {}),
        ...(opts.format ? { format: opts.format as OutputFormat } : {}),
        ...(opts.quiet ? { quiet: opts.quiet } : {}),
        ...(opts.base ? { base: opts.base } : {}),
        ...(opts.changedOnly ? { changedOnly: opts.changedOnly } : {}),
      });
      process.exit(exitCode);
    });
}
