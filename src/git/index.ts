/**
 * Git Module Public API
 *
 * Git連携機能の公開インターフェース。
 * 外部からは本ファイル経由でのみアクセスする。
 */

// 型定義
export type {
  GitError,
  ChangedFile,
  DetectionTarget,
  DocIdChange,
  ChangeDetectionResult,
  GitOperations,
  GitOperationsConfig,
} from './types';

// 実装クラス・ファクトリ
export { SimpleGitOperations, createGitOperations } from './operations';

// 変更検出器
export { ChangeDetector, createChangeDetector } from './change-detector';
