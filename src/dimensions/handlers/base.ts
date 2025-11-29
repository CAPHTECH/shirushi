/**
 * Dimension Handler Base Interface
 *
 * 各 dimension type (enum, year, serial, checksum 等) のハンドラが実装する
 * 共通インターフェースを定義します。
 *
 * LDE準拠: Either型で成功/失敗を表現し、副作用を排除
 */

import { type Either } from 'fp-ts/Either';

import type { DimensionDefinition } from '@/config/schema';
import type { IndexEntry } from '@/core/index-manager';
import type { ShirushiErrorCode } from '@/errors/definitions';
import type { TemplateParseResult } from '@/parsers/template';
import type { DocumentMetadata } from '@/types/document';

// Dimension型
export type Dimension = DimensionDefinition;

/**
 * 検証エラー情報
 * 法則違反を構造化して表現
 */
export interface ValidationError {
  code: ShirushiErrorCode;
  message: string;
  dimensionName: string;
  value: string;
  expected?: string;
  context?: Record<string, unknown>;
}

/**
 * 生成エラー情報
 * ID生成時の法則違反を表現
 */
export interface GenerationError {
  code: ShirushiErrorCode;
  message: string;
  dimensionName: string;
  context?: Record<string, unknown>;
}

/**
 * 検証コンテキスト
 * ハンドラが検証時に参照する追加情報
 */
export interface ValidationContext {
  /** ドキュメントのファイルパス（リポジトリルートからの相対パス） */
  documentPath: string;
  /** ドキュメントのメタデータ（doc_type, created_at等） */
  documentMeta: DocumentMetadata;
  /** 他のdimension値（checksum検証用） */
  parsedParts: Record<string, string>;
  /** dimension名 */
  dimensionName: string;
}

/**
 * 生成コンテキスト
 * ID生成時に参照する情報
 */
export interface GenerationContext {
  /** ドキュメントのファイルパス */
  documentPath: string;
  /** ドキュメントのメタデータ */
  documentMeta: DocumentMetadata;
  /** 他のdimension値（serial採番、checksum計算用） */
  otherParts: Record<string, string>;
  /** dimension名 */
  dimensionName: string;
  /** インデックスエントリ（serial採番用、optional） */
  indexEntries?: IndexEntry[];
  /** テンプレート解析結果（serial採番用、optional） */
  templateResult?: TemplateParseResult;
}

/**
 * Dimension Handler Interface
 *
 * 各dimension typeはこのインターフェースを実装する。
 * - validate: doc_id内の値を検証
 * - generate: 新しいID用の値を生成
 * - toPattern: 正規表現パターンを生成
 */
export interface DimensionHandler<T extends Dimension = Dimension> {
  /**
   * dimension値を検証
   *
   * @param value - doc_idから抽出された値
   * @param dimension - dimension定義
   * @param context - 検証コンテキスト
   * @returns 検証成功時はRight(true)、失敗時はLeft(ValidationError)
   */
  validate(
    value: string,
    dimension: T,
    context: ValidationContext
  ): Either<ValidationError, true>;

  /**
   * dimension値を生成
   *
   * @param dimension - dimension定義
   * @param context - 生成コンテキスト
   * @returns 生成成功時はRight(value)、失敗時はLeft(GenerationError)
   */
  generate(
    dimension: T,
    context: GenerationContext
  ): Either<GenerationError, string>;

  /**
   * 正規表現パターンを生成
   *
   * @param dimension - dimension定義
   * @returns 正規表現パターン文字列（キャプチャグループ付き）
   */
  toPattern(dimension: T): string;
}

/**
 * ハンドラファクトリ型
 * DimensionRegistryで使用
 */
export type DimensionHandlerFactory = () => DimensionHandler;
