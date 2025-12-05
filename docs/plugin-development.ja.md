# プラグイン開発ガイド

このガイドでは、Shirushi用のプラグイン作成方法を説明します。プラグインを使用すると、カスタムのドキュメントソース、インデックスストア、変更トラッカーを実装してShirushiの機能を拡張できます。

## 概要

Shirushiのプラグインアーキテクチャは3つのコアインターフェースで構成されています：

| インターフェース | 目的 | 使用例 |
|------------------|------|--------|
| `DocumentSource` | ドキュメントの取得と列挙 | PostgreSQL、MongoDB、Notion API |
| `IndexStore` | インデックスの永続化とクエリ | SQLite、Redis、DynamoDB |
| `ChangeTracker` | 変更検出 | 監査ログ、タイムスタンプ、Webhook |

プラグインはこれらのインターフェースを1つ以上実装できます。

## クイックスタート

### 最小構成のプラグイン

```typescript
import type { ShirushiPlugin } from '@shirushi/core';

const myPlugin: ShirushiPlugin = {
  name: 'my-plugin',
  version: '1.0.0',
};

export default myPlugin;
```

### DocumentSourceを持つプラグイン

```typescript
import { right, left } from 'fp-ts/Either';
import type {
  ShirushiPlugin,
  DocumentSource,
  DocumentReference,
  DocumentContent,
  DocumentFilter,
  DocumentSourceError,
} from '@shirushi/core';

class MyDocumentSource implements DocumentSource {
  readonly name = 'my-document-source';

  async *listDocuments(filter?: DocumentFilter): AsyncIterable<DocumentReference> {
    // データソースからドキュメントを取得
    const documents = await this.fetchDocuments(filter);

    for (const doc of documents) {
      yield {
        id: doc.id,
        displayPath: doc.path,
        kind: 'markdown',
      };
    }
  }

  async getDocument(
    ref: DocumentReference
  ): Promise<Either<DocumentSourceError, DocumentContent | null>> {
    try {
      const content = await this.fetchContent(ref.id);

      if (!content) {
        return right(null);
      }

      return right({
        ref,
        docId: content.doc_id,
        metadata: {
          title: content.title,
          doc_type: content.type,
        },
        rawContent: content.body,
      });
    } catch (error) {
      return left({
        code: 'DOCUMENT_READ_ERROR',
        message: `ドキュメントの読み取りに失敗しました: ${ref.id}`,
        context: {
          documentId: ref.id,
          originalError: String(error),
        },
      });
    }
  }

  private async fetchDocuments(filter?: DocumentFilter) {
    // データ取得ロジックを実装
    return [];
  }

  private async fetchContent(id: string) {
    // コンテンツ取得ロジックを実装
    return null;
  }
}

const myPlugin: ShirushiPlugin = {
  name: 'my-document-source-plugin',
  version: '1.0.0',
  documentSource: new MyDocumentSource(),
};

export default myPlugin;
```

## コアインターフェース

### DocumentSource

任意のデータソースからのドキュメント取得を抽象化します。

```typescript
interface DocumentSource {
  /** ログ出力用のソース名 */
  readonly name: string;

  /** フィルタに一致するドキュメントを列挙 */
  listDocuments(filter?: DocumentFilter): AsyncIterable<DocumentReference>;

  /** 参照からドキュメントコンテンツを取得 */
  getDocument(
    ref: DocumentReference
  ): Promise<Either<DocumentSourceError, DocumentContent | null>>;

  /** ドキュメントを更新（オプション、assignコマンド用） */
  updateDocument?(
    ref: DocumentReference,
    options: DocumentUpdateOptions
  ): Promise<Either<DocumentSourceError, void>>;

  /** ヘルスチェック（オプション） */
  healthCheck?(): Promise<HealthCheckResult>;
}
```

#### 主要な型

```typescript
interface DocumentReference {
  readonly id: string;           // 一意識別子
  readonly displayPath: string;  // 人間可読なパス
  readonly kind: DocumentKind;   // 'markdown' | 'yaml'
}

interface DocumentContent {
  readonly ref: DocumentReference;
  readonly docId: string | null;           // 抽出されたdoc_id
  readonly metadata: DocumentMetadata;     // パース済みメタデータ
  readonly rawContent?: string;            // 更新用の生コンテンツ
}

interface DocumentFilter {
  readonly patterns?: readonly string[];   // Globパターン
  readonly paths?: readonly string[];      // 特定のパス
  readonly metadata?: Record<string, unknown>;
  readonly modifiedAfter?: Date;
}
```

### IndexStore

インデックスの永続化とクエリを抽象化します。

```typescript
interface IndexStore {
  readonly name: string;

  /** doc_idでエントリを取得 */
  getByDocId(docId: string): Promise<Either<IndexStoreError, PluginIndexEntry | null>>;

  /** パスでエントリを取得 */
  getByPath(path: string): Promise<Either<IndexStoreError, PluginIndexEntry | null>>;

  /** すべてのエントリを列挙 */
  listEntries(): AsyncIterable<PluginIndexEntry>;

  /** エントリを追加または更新 */
  upsert(entry: PluginIndexEntry): Promise<Either<IndexStoreError, void>>;

  /** エントリを削除 */
  delete(docId: string): Promise<Either<IndexStoreError, boolean>>;

  /** 重複doc_idを検出 */
  findDuplicates(): Promise<Either<IndexStoreError, DuplicateReport>>;

  /** 孤立エントリを検出（オプション） */
  findOrphans?(
    documentPaths: readonly string[]
  ): Promise<Either<IndexStoreError, readonly string[]>>;
}
```

#### 主要な型

```typescript
interface PluginIndexEntry {
  readonly docId: string;
  readonly path: string;
  readonly title?: string;
  readonly docType?: string;
  readonly status?: string;
  readonly version?: string;
  readonly owner?: string;
  readonly tags?: readonly string[];
  readonly extra?: Record<string, unknown>;  // プラグイン固有のデータ
}
```

### ChangeTracker

変更検出メカニズムを抽象化します。

```typescript
interface ChangeTracker {
  readonly name: string;

  /** 基準参照からの変更を検出 */
  detectChanges(
    baseRef: string,
    source: DocumentSource
  ): Promise<Either<ChangeTrackerError, PluginChangeDetectionResult>>;

  /** トラッカーが利用可能かチェック */
  isAvailable(): Promise<boolean>;

  /** 参照を検証（オプション） */
  isValidRef?(ref: string): Promise<boolean>;
}
```

## エラーハンドリング

すべての非同期メソッドはfp-tsの`Either<Error, Success>`を返します：

```typescript
import { right, left, isRight, isLeft } from 'fp-ts/Either';

// 成功
return right(result);

// 失敗
return left({
  code: 'ERROR_CODE',
  message: '人間可読なメッセージ',
  context: {
    // デバッグ用の追加コンテキスト
  },
});

// 結果のハンドリング
const result = await source.getDocument(ref);
if (isLeft(result)) {
  console.error(`エラー: ${result.left.message}`);
} else {
  console.log(`ドキュメント: ${result.right?.docId}`);
}
```

### エラー型

```typescript
interface DocumentSourceError {
  readonly code: string;
  readonly message: string;
  readonly context?: {
    readonly documentId?: string;
    readonly displayPath?: string;
    readonly originalError?: string;
  };
}

interface IndexStoreError {
  readonly code: string;
  readonly message: string;
  readonly context?: {
    readonly docId?: string;
    readonly path?: string;
    readonly originalError?: string;
  };
}

interface ChangeTrackerError {
  readonly code: string;
  readonly message: string;
  readonly context?: {
    readonly baseRef?: string;
    readonly path?: string;
    readonly originalError?: string;
  };
}
```

## プラグインライフサイクル

```typescript
interface ShirushiPlugin {
  readonly name: string;
  readonly version: string;

  readonly documentSource?: DocumentSource;
  readonly indexStore?: IndexStore;
  readonly changeTracker?: ChangeTracker;

  /** プラグインロード時に呼び出される */
  initialize?(config: PluginConfig): Promise<void>;

  /** プラグインアンロード時に呼び出される */
  dispose?(): Promise<void>;
}
```

### ライフサイクル付きの例

```typescript
class PostgresPlugin implements ShirushiPlugin {
  readonly name = '@shirushi/plugin-postgres';
  readonly version = '1.0.0';

  private pool: Pool | null = null;
  documentSource?: PostgresDocumentSource;
  indexStore?: PostgresIndexStore;

  async initialize(config: PluginConfig): Promise<void> {
    this.pool = new Pool({
      connectionString: config.connectionString as string,
    });

    await this.pool.connect();

    this.documentSource = new PostgresDocumentSource(this.pool);
    this.indexStore = new PostgresIndexStore(this.pool);
  }

  async dispose(): Promise<void> {
    await this.pool?.end();
    this.pool = null;
  }
}
```

## 型ガード

型ガードを使用してランタイムでプラグインの機能をチェックできます：

```typescript
import {
  isDocumentSource,
  isIndexStore,
  isChangeTracker,
  hasDocumentSource,
  hasIndexStore,
  hasChangeTracker,
  isUpdatableDocumentSource,
  isOrphanDetectableIndexStore,
} from '@shirushi/core';

// オブジェクトがDocumentSourceかチェック
if (isDocumentSource(obj)) {
  // objはDocumentSource型として使用可能
}

// プラグインがDocumentSourceを提供しているかチェック
if (hasDocumentSource(plugin)) {
  // plugin.documentSourceはDocumentSource型
}

// オプショナルな機能のチェック
if (isUpdatableDocumentSource(source)) {
  // source.updateDocumentが利用可能
}
```

## ベストプラクティス

### 1. 配列の防御的コピー

```typescript
// 悪い例: 参照の共有
return {
  tags: entry.tags,  // 呼び出し側で変更される可能性
};

// 良い例: 防御的コピー
return {
  tags: entry.tags ? [...entry.tags] : undefined,
};
```

### 2. 大規模データセットにはAsyncIterableを使用

```typescript
// 良い例: メモリ効率の良いストリーミング
async *listDocuments(): AsyncIterable<DocumentReference> {
  let offset = 0;
  const batchSize = 100;

  while (true) {
    const batch = await this.fetchBatch(offset, batchSize);
    if (batch.length === 0) break;

    for (const doc of batch) {
      yield doc;
    }

    offset += batchSize;
  }
}
```

### 3. 意味のあるエラーコンテキストを提供

```typescript
return left({
  code: 'CONNECTION_FAILED',
  message: 'PostgreSQLへの接続に失敗しました',
  context: {
    host: config.host,
    port: config.port,
    originalError: error.message,
    // パスワードなどの機密データは含めない！
  },
});
```

### 4. ヘルスチェックを実装

```typescript
async healthCheck(): Promise<HealthCheckResult> {
  try {
    await this.pool.query('SELECT 1');
    return { ok: true };
  } catch (error) {
    return {
      ok: false,
      message: `データベース接続に失敗: ${error.message}`,
    };
  }
}
```

## 既知の制限事項

1. **AsyncIterableのエラーハンドリング**: `listDocuments()`と`listEntries()`はストリーム途中で構造化されたエラーを返せません。ストリームエラーには例外をスローしてください。

2. **型ガードの制限**: 型ガードはプロパティの存在のみを検証し、戻り値の型は検証しません。実装が正しい型を返すことを確認してください。

3. **`extra`フィールド**: `PluginIndexEntry.extra`はプラグイン内部での使用を目的としており、YAMLインデックスファイルには永続化されません。

詳細な設計決定と根拠については[ADR-0008](./adr/0008-plugin-architecture.md)を参照してください。

## サンプル

### PostgreSQL DocumentSource

[examples/plugin-postgres/](../examples/plugin-postgres/)を参照（Phase 4で追加予定）

### SQLite IndexStore

[examples/plugin-sqlite/](../examples/plugin-sqlite/)を参照（Phase 4で追加予定）

## APIリファレンス

完全なTypeScript APIドキュメントはソースファイルで確認できます：

- [`src/plugins/interfaces/document-source.ts`](../src/plugins/interfaces/document-source.ts)
- [`src/plugins/interfaces/index-store.ts`](../src/plugins/interfaces/index-store.ts)
- [`src/plugins/interfaces/change-tracker.ts`](../src/plugins/interfaces/change-tracker.ts)
- [`src/plugins/types.ts`](../src/plugins/types.ts)
