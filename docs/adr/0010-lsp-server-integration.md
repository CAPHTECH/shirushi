---
doc_id: SHI-ADR-2025-0010-F
title: "ADR-0010: LSP Server Integration for @see docid Navigation"
version: "1.0.0"
status: Accepted
created_at: 2025-12-21
---

# ADR-0010: LSP Server Integration for @see docid Navigation

**Status**: Accepted

**Date**: 2025-12-21

**Deciders**: CAPHTECH Team

**Tags**: lsp, developer-experience, integration

---

## Context

ShirushiはドキュメントID管理システムであり、コード内の `@see docid` コメントからドキュメントへの参照を可能にしている。現状では、開発者がdoc_idを見つけても、対応するドキュメントファイルを手動で検索する必要がある。

Claude Code v2.0.74以降では、カスタムLSPサーバーをプラグインとして統合でき、以下のLSP操作をサポートしている：

- `goToDefinition`: シンボル定義へのジャンプ
- `hover`: シンボル上でのドキュメント表示
- `findReferences`: シンボルの参照一覧取得

この機能を活用することで、`@see PCE-SPEC-2025-0001-G` のようなコメント上でCtrl+Clickすると、対応するドキュメントファイルへジャンプできるようになる。

### 制約

1. stdio transportを使用する必要がある（Claude Code互換）
2. 既存のTypeScript Language Serverと共存する必要がある
3. 全ソースファイルタイプで動作する必要がある（コメント構文は言語に依存しない `@see` パターンを使用）

## Decision

ShirushiをLSPサーバーとして実装し、以下の機能を提供する。

### 実装方針

1. **vscode-languageserver パッケージを使用**
   - `vscode-languageserver` (v9.x)
   - `vscode-languageserver-textdocument` (v1.x)
   - stdio transportで通信

2. **対応するLSPメソッド**

   | メソッド | 機能 |
   |---------|------|
   | `goToDefinition` | `@see docid` → ドキュメントファイルへジャンプ |
   | `hover` | doc_id上でドキュメントタイトル・概要を表示 |
   | `findReferences` | doc_idを参照しているソースファイル一覧 |

3. **認識パターン**

   デフォルトパターン: `@see {doc_id}`

   設定で拡張可能:
   ```yaml
   source_ref_patterns:
     - "@see {doc_id}"
     - "@ref {doc_id}"
   ```

4. **既存コア機能の再利用**
   - `lookupDocument`: doc_id → ドキュメント情報取得
   - `buildIdPattern`: id_formatから正規表現パターン生成
   - `scanSourceReferences`: ソースコード内のdoc_id参照検出

5. **ディレクトリ構造**
   ```
   src/
   └── lsp/
       ├── server.ts      # LSPサーバーメイン
       ├── handlers/
       │   ├── definition.ts   # goToDefinition
       │   ├── hover.ts        # hover
       │   └── references.ts   # findReferences
       └── utils/
           └── pattern-matcher.ts  # doc_idパターンマッチング
   ```

6. **CLIコマンド**
   ```bash
   shirushi lsp  # LSPサーバーを起動（stdio transport）
   ```

### Claude Code プラグイン設定

```json
// .lsp.json
{
  "shirushi": {
    "command": "shirushi",
    "args": ["lsp"],
    "extensionToLanguage": {
      ".ts": "typescript",
      ".tsx": "typescriptreact",
      ".js": "javascript",
      ".py": "python",
      ".rs": "rust",
      ".go": "go"
    }
  }
}
```

## Alternatives Considered

### 1. MCP統合のみ（Issue #24）

**説明**: MCPツールとしてdoc_id検索機能を提供

**利点**:
- AI側から能動的にドキュメントを検索可能
- リソースとしてドキュメントコンテンツを公開可能

**欠点**:
- 開発者の「Ctrl+Click」ナビゲーション体験を提供できない
- コードエディタ統合にはLSPが必要

**結論**: MCPとLSPは補完的であり、両方実装する（Issue #24とは独立）

### 2. VSCode拡張機能として実装

**説明**: VSCode専用の拡張機能として実装

**利点**:
- VSCodeのフル機能を活用可能
- より豊富なUI/UX

**欠点**:
- VSCode専用となり、他のエディタ/CLIツールで使用不可
- Claude Code統合にはLSPが必要

**結論**: LSPは標準プロトコルであり、より広い互換性を提供

## Consequences

### Positive

- **開発者体験の向上**: `@see docid` からワンクリックでドキュメントへジャンプ
- **コードレビュー効率化**: 参照先ドキュメントへ即座にアクセス可能
- **Claude Code統合**: AIと人間が同じナビゲーション体験を共有
- **エディタ非依存**: LSP対応エディタであれば利用可能

### Negative

- **依存関係の増加**: vscode-languageserverパッケージの追加
- **設定の複雑化**: .lsp.json設定が必要
- **既存LSPとの競合リスク**: 同一言語に複数LSPが存在する場合の挙動確認が必要

### Neutral

- **パフォーマンス**: 大規模プロジェクトでのdoc_indexロード時間は設定次第
- **メンテナンスコスト**: LSP仕様の変更への追従が必要

## Related Decisions

- ADR-0003: Document is Source of Truth for doc_id
- ADR-0008: Plugin Architecture for External System Integration
- Issue #24: MCP統合（補完関係）
- Issue #26: 本ADRの実装Issue

## Notes

### 参考資料

- [VS Code Language Server Extension Guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide)
- [vscode-languageserver-node](https://github.com/microsoft/vscode-languageserver-node)
- [Claude Code LSP Support](https://azukiazusa.dev/blog/claude-code-lsp-support/)

### 将来の拡張

1. **Diagnostics**: doc_id参照のリアルタイム検証
2. **CodeLens**: ドキュメント参照数の表示
3. **コード補完**: doc_id入力時の候補表示（autoCompleteはClaude Code未対応のため将来対応）
