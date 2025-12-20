import { z } from 'zod';

/**
 * デフォルトのIDフィールド名
 *
 * doc_id以外のフィールド名を使用する場合は、設定ファイルのid_fieldで指定する。
 */
export const DEFAULT_ID_FIELD = 'doc_id' as const;

const GlobSchema = z.string().min(1, 'doc_globs must contain non-empty strings');

// 各dimension schemaをexport（他モジュールからの型推論用）
export const EnumDimensionSchema = z.object({
  type: z.literal('enum'),
  values: z.array(z.string().min(1)).min(1),
  select: z
    .object({
      by_path: z
        .array(
          z.object({
            pattern: z.string().min(1),
            value: z.string().min(1),
          })
        )
        .min(1),
    })
    .optional(),
});

export const EnumFromDocTypeDimensionSchema = z.object({
  type: z.literal('enum_from_doc_type'),
  mapping: z.record(z.string().min(1)).refine(
    (mapping) => Object.keys(mapping).length > 0,
    'mapping must contain at least one entry'
  ),
});

export const YearDimensionSchema = z.object({
  type: z.literal('year'),
  digits: z.number().int().min(2).max(4).default(4),
  source: z.string().min(1).default('created_at'),
});

export const SerialDimensionSchema = z.object({
  type: z.literal('serial'),
  digits: z.number().int().min(1),
  scope: z.array(z.string().min(1)).min(1),
});

export const ChecksumDimensionSchema = z.object({
  type: z.literal('checksum'),
  algo: z.enum(['mod26AZ']),
  of: z.array(z.string().min(1)).min(1),
});

export const DimensionSchema = z.discriminatedUnion('type', [
  EnumDimensionSchema,
  EnumFromDocTypeDimensionSchema,
  YearDimensionSchema,
  SerialDimensionSchema,
  ChecksumDimensionSchema,
]);

/**
 * 参照パターン定義スキーマ
 *
 * Issue #15: doc_id変更時の文書間参照整合性チェック機能
 *
 * pattern内の {DOC_ID} は id_format から生成される正規表現パターンに展開される。
 * 例: "\\[.*?\\]\\({DOC_ID}\\)" → Markdownリンク [text](doc_id) を検出
 */
export const ReferencePatternSchema = z.object({
  /** パターン名（識別用） */
  name: z.string().min(1),
  /** 正規表現パターン。{DOC_ID} をプレースホルダーとして使用可能 */
  pattern: z.string().min(1),
});

/**
 * ソースコード参照パターン定義スキーマ
 *
 * ソースコード内でドキュメントを参照しているパターンを検出する。
 * pattern内の {DOC_ID} は id_format から生成される正規表現パターンに展開される。
 */
export const SourceReferencePatternSchema = z.object({
  /** 対象ファイルのglobパターン */
  glob: z.string().min(1),
  /** 正規表現パターン。{DOC_ID} をプレースホルダーとして使用可能 */
  pattern: z.string().min(1),
});

/**
 * コンテンツ整合性設定スキーマ
 *
 * ドキュメント本文のハッシュを計算・検証し、改ざんを検出する。
 */
export const ContentIntegritySchema = z.object({
  /** コンテンツ整合性チェックを有効化 */
  enabled: z.boolean().default(false),
  /** ハッシュアルゴリズム（現在はsha256のみ） */
  algorithm: z.enum(['sha256']).default('sha256'),
  /** ソースコード内の参照を検出するパターン */
  source_references: z.array(SourceReferencePatternSchema).optional(),
});

/**
 * チェックサム設定スキーマ（新形式）
 *
 * ADR-0009: チェックサムをdoc_idから分離して別フィールドに
 * doc_idとは別にchecksumフィールドで管理する。
 *
 * @see docs/adr/0009-separate-checksum-from-doc-id.md
 */
export const ChecksumConfigSchema = z.object({
  /** ドキュメント内のチェックサムフィールド名（デフォルト: "checksum"） */
  field: z.string().min(1).default('checksum'),
  /** チェックサムアルゴリズム（現在は mod26AZ のみ） */
  algo: z.enum(['mod26AZ']),
  /** チェックサム計算の対象となるdimension名の配列 */
  of: z.array(z.string().min(1)).min(1),
});

export const ConfigSchema = z
  .object({
    id_format: z.string().min(1, 'id_format must not be empty'),
    doc_globs: z.array(GlobSchema).min(1, 'doc_globs must contain at least one glob'),
    dimensions: z.record(DimensionSchema).refine(
      (dimensions) => Object.keys(dimensions).length > 0,
      'dimensions must contain at least one definition'
    ),
    index_file: z.string().default('docs/doc_index.yaml'),
    id_field: z
      .string()
      .min(1, 'id_field must not be empty')
      .regex(/^[a-zA-Z_][a-zA-Z0-9_]*$/, 'id_field must be a valid identifier')
      .default(DEFAULT_ID_FIELD),
    forbid_id_change: z.boolean().default(true),
    allow_missing_id_in_new_files: z.boolean().default(false),

    // Issue #15: 参照整合性チェック設定
    /**
     * 参照を含む可能性のあるYAMLフィールド名
     * 例: ["superseded_by", "related_docs"]
     */
    reference_fields: z.array(z.string().min(1)).default(['superseded_by']),

    /**
     * 参照パターン定義
     * 各パターンの pattern 内で {DOC_ID} を使用可能。
     * デフォルトではMarkdownリンク形式を検出。
     */
    reference_patterns: z
      .array(ReferencePatternSchema)
      .default([{ name: 'markdown_link', pattern: '\\[.*?\\]\\({DOC_ID}\\)' }]),

    /**
     * コンテンツ整合性チェック設定
     * ドキュメント本文のハッシュを検証し、改ざんを検出する。
     */
    content_integrity: ContentIntegritySchema.optional(),

    /**
     * チェックサム設定（新形式）
     *
     * ADR-0009: チェックサムをdoc_idから分離して別フィールドに
     * この設定がある場合、doc_idにはチェックサムを含めず、
     * 別フィールド（デフォルト: checksum）で管理する。
     *
     * @see docs/adr/0009-separate-checksum-from-doc-id.md
     */
    checksum: ChecksumConfigSchema.optional(),
  })
  .superRefine((config, ctx) => {
    const placeholders = extractTemplatePlaceholders(config.id_format);
    const rawSegments = extractRawPlaceholderSegments(config.id_format);
    const invalidNames = rawSegments.filter((name) => !PLACEHOLDER_NAME_PATTERN.test(name));

    if (invalidNames.length > 0) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ['id_format'],
        message: `id_format contains invalid placeholder names: ${invalidNames.join(', ')}`,
      });
    }

    if (placeholders.length === 0 && invalidNames.length === 0) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ['id_format'],
        message: 'id_format must contain at least one placeholder {PLACEHOLDER}',
      });
    }

    const openBraces = (config.id_format.match(/\{/g) || []).length;
    const closeBraces = (config.id_format.match(/\}/g) || []).length;
    if (openBraces !== closeBraces) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ['id_format'],
        message: 'id_format has unbalanced braces',
      });
    }

    const dimensionNames = new Set(Object.keys(config.dimensions));

    const undefinedPlaceholders = placeholders.filter((name) => !dimensionNames.has(name));
    if (undefinedPlaceholders.length > 0) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ['id_format'],
        message: `id_format references undefined dimensions: ${undefinedPlaceholders.join(', ')}`,
      });
    }

    placeholders.forEach((name) => {
      if (config.dimensions[name]?.type === 'enum_from_doc_type' && name === 'doc_type') {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ['dimensions', name],
          message: 'dimension name doc_type is reserved',
        });
      }
    });

    // 参照パターンの正規表現構文を検証
    for (let i = 0; i < config.reference_patterns.length; i++) {
      const pattern = config.reference_patterns[i];
      if (pattern) {
        try {
          // {DOC_ID} を仮のパターンに置換して正規表現として有効かチェック
          const testPattern = pattern.pattern.replace(/\{DOC_ID\}/g, '.*');
          new RegExp(testPattern);
        } catch {
          ctx.addIssue({
            code: z.ZodIssueCode.custom,
            path: ['reference_patterns', i, 'pattern'],
            message: `Invalid regex pattern: ${pattern.pattern}`,
          });
        }
      }
    }

    // ADR-0009: checksum設定の検証
    // id_format内のchecksum dimensionと、新形式checksum設定の競合をチェック
    const hasChecksumInDimensions = Object.values(config.dimensions).some(
      (dim) => dim.type === 'checksum'
    );
    const hasChecksumConfig = config.checksum !== undefined;

    if (hasChecksumInDimensions && hasChecksumConfig) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ['checksum'],
        message:
          'Cannot use both checksum dimension in id_format and separate checksum config. ' +
          'Please migrate to the new format (ADR-0009).',
      });
    }

    // 新形式checksum設定の場合、ofで指定されたdimensionが存在するか検証
    if (hasChecksumConfig && config.checksum) {
      for (const dimName of config.checksum.of) {
        if (!config.dimensions[dimName]) {
          ctx.addIssue({
            code: z.ZodIssueCode.custom,
            path: ['checksum', 'of'],
            message: `checksum.of references undefined dimension: ${dimName}`,
          });
        }
      }
    }
  });

export type ShirushiConfig = z.infer<typeof ConfigSchema>;
export type DimensionDefinition = ShirushiConfig['dimensions'][string];
export type ReferencePattern = z.infer<typeof ReferencePatternSchema>;
export type ChecksumConfig = z.infer<typeof ChecksumConfigSchema>;

const PLACEHOLDER_REGEX = /\{([A-Za-z0-9_]+)\}/g;
const RAW_PLACEHOLDER_REGEX = /\{([^}]*)\}/g;
const PLACEHOLDER_NAME_PATTERN = /^[A-Za-z0-9_]+$/;

export function extractTemplatePlaceholders(template: string): string[] {
  PLACEHOLDER_REGEX.lastIndex = 0;
  const matches: string[] = [];
  const seen = new Set<string>();
  let result: RegExpExecArray | null;
  while ((result = PLACEHOLDER_REGEX.exec(template)) !== null) {
    const name = result[1];
    if (name !== undefined && !seen.has(name)) {
      seen.add(name);
      matches.push(name);
    }
  }
  return matches;
}

function extractRawPlaceholderSegments(template: string): string[] {
  RAW_PLACEHOLDER_REGEX.lastIndex = 0;
  const matches: string[] = [];
  let result: RegExpExecArray | null;
  while ((result = RAW_PLACEHOLDER_REGEX.exec(template)) !== null) {
    matches.push(result[1] ?? '');
  }
  return matches;
}
