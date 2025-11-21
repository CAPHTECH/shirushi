<!-- Doc-ID: DOC-RULES-LAW-DRIVEN-ENGINEERING -->

# Law-Driven Engineering (LDE)

**Law-Driven Engineering（法則駆動工学）**は、ビジネスルールや制約を「法則」として捉え、実装の一貫性と保守性を高めるソフトウェア開発手法です。従来のLDEに**構造化概念**を統合し、**自己進化システム**、**法則ドメイン管理**、**制約伝播ネットワーク**により、数学的厳密性と実用的構造化を両立します。

## 🎯 実践第一のアプローチ

**重要**: LDEは必要に応じて段階的に適用します。すべてのコードに重厚な理論を適用する必要はありません。

### 基本指針
1. **YAGNI (You Aren't Gonna Need It)**: 複雑な形式化は本当に必要になってから適用
2. **KISS (Keep It Simple, Stupid)**: シンプルな解決策を優先し、複雑さは段階的に追加
3. **Library First**: サードパーティライブラリを活用し、車輪の再発明を避ける
4. **Immutability First**: 全てのデータを不変として扱い、変換により新しい状態を生成
5. **Pure Functions**: 副作用のない純粋関数を基本とし、関数合成で複雑な処理を構築
6. **Compositional Design**: 小さな関数を組み合わせて大きな機能を実現

## 🔢 YAGNI/KISSの数学的定義

LDEでは、実践的原則であるYAGNI/KISSも数学的に表現し、生成AIが効率的に解釈・適用できる形式で定義します。

### YAGNI Score (実装適切性指標)

```mathematical
YAGNI_Score = Used_Features / Implemented_Features

where:
- Used_Features: 実際に使用されている機能数
- Implemented_Features: 実装済み機能数
- Target: YAGNI_Score ≥ 0.8 (80%以上が使用されている)
```

**測定方法**:
- 静的解析: 呼び出されない関数・クラスの検出
- 動的解析: 実行時カバレッジの測定

### KISS Score (シンプルさ指標)

```mathematical
KISS_Score = 1 / (1 + Normalized_Complexity)

Normalized_Complexity = (CC + CD + CF) / 3

where:
- CC: Cyclomatic Complexity (正規化済み)
- CD: Dependency Complexity (正規化済み) 
- CF: Function Complexity (正規化済み)
- Target: KISS_Score ≥ 0.7
```

## 🏗️ LDE: 5つの統合構造化概念

LDEは以下の5つの構造化概念を統合し、実用的な大規模システム構築を可能にします：

### 1. **法則ドメイン（Law Domain）** - DDDとの統合
- **法則境界**: 異なる法則体系によるドメイン分離
- **法則集約**: 関連する法則群をAggregateとして管理
- **法則コンテキスト**: Bounded Contextを法則の適用範囲で定義

### 2. **階層射影（Layer Projection）** - 圏論的構造化
- **構造射**: 各層間でのデータ構造変換の明示
- **不変射**: 層を跨いでも保持すべき性質の定義
- **合成射**: 法則→実装への直接変換パスの最適化

### 3. **法則モジュール（Law Module）** - 関数型モジュラー設計
- **法則インターフェース**: 法則の公開契約の明示
- **法則依存**: モジュール間の法則レベルでの依存関係
- **法則合成**: 小さな法則モジュールから大きなシステムの構築

### 4. **制約伝播ネットワーク（Constraint Propagation Network）**
- **制約グラフ**: 法則間の依存関係をグラフ構造で表現
- **影響分析**: 法則変更時の波及効果の自動分析
- **制約分離**: 独立な制約群によるモジュール境界の決定

### 5. **適応的アーキテクチャ（Adaptive Architecture）**
- **Simple→Standard→Complex**: 段階的な構造複雑化
- **法則密度**: 単位あたりの法則複雑度による構造決定
- **進化的分離**: システム成長に伴う自然な境界の発生

## LDEの3つのトラック

プロジェクトの複雑性と要件に応じて適切なトラックを選択：

| トラック | 対象 | アプローチ | 複雑度 |
|---------|------|-----------|----------|
| **Simple** | CRUD、単純なビジネスロジック | 基本的なバリデーション + 既存ライブラリ | 低 |
| **Standard** | 複雑なビジネスルール、状態管理 | 型安全性 + Property-based testing | 中 |
| **Complex** | ミッションクリティカル、分散システム | 形式仕様 + 数学的検証 | 高 |

## LDEの理論的基盤

### 記号接地とカッシーラーの実体概念/関数概念

LDEは、カッシーラーの区別する**実体概念（Substance）**と**関数概念（Function）**において、後者（関係・写像・法則）を一次要素として採用します。これにより、オブジェクト中心（実体概念）で生じがちな記号接地の曖昧さを、観測可能量と検証可能性で埋め合わせます。

#### 記号接地（Grounding）の操作的定義

```mathematical
Let O be the set of Observables (logs, domain events, metrics, UI traces).

Grounded(term)    ⇔ term ∈ Vocabulary ∧ ∃m ∈ Measurements: maps(term, m) ∧ m ∈ O
Grounded(law)     ⇔ ∃(P ∨ R): P ∈ PropertyTests ∨ R ∈ RuntimeAssertions ∧ observational_map(law, O)
```

実務指針:
- **Relation-First**: 関係・制約・法則を先に定義し、型・データはその結果として派生させる
- **観測写像**: すべての pre/post/inv を、少なくとも1つの Observable または Property と対応付ける

### 拡張5層アーキテクチャ

LDEは既存の3層に構造層と適応層を追加した5層で構成されます：

| 層 | 役割 | 抽象度 | 強化する側面 |
|---|---|---|---|
| **法則層（Law Layer）** | 哲学・世界観 (Why) | 高 | 概念的整合性、アーキテクチャの一貫性 |
| **形式層（Formal Layer）** | モデル化・分析 (How) | 中-高 | 仕様の厳密性、設計の正確性、性能評価 |
| **🏗️構造層（Structural Layer）** | モジュール・境界 (What) | 中 | システム境界、モジュール分離、依存管理 |
| **実装層（Implementation Layer）** | 実装・検証 (How) | 低 | 実装の堅牢性、コードレベルの正しさ保証 |
| **🔄適応層（Adaptive Layer）** | 進化・監視 (When) | 低-動的 | 構造進化、パフォーマンス監視、自動適応 |

## 🧮 関数型プログラミングとLDEの概念対応

### 「法則」と「純粋関数」の本質的同一性

LDEの「法則」と関数型プログラミングの「純粋関数」は、数学的な**写像（mapping）**として共通の性質を持ちます。これにより、**ビジネス法則を純粋関数として直接実装**することが可能になります。

- **LDE（法則）**: ビジネス条件 → ビジネス結果（確定的関係）
- **FP（純粋関数）**: 引数 → 戻り値（副作用なし・参照透明）

### 「不変条件」と「不変性」の統一的理解

両者は「**制御された状態変化**」という共通目的を異なるレベルで実現し、相互に強化します。

- **意味レベル（LDE）**: ビジネス意味での整合性保証（例：残高はマイナスにならない）
- **実装レベル（関数型）**: データ構造での安全性保証（例：オブジェクトは変更不可）

## LDE詳細プロセス

### Phase 0: 現象把握と法則探求（多重表象による問題分析）
1. **変数の列挙**: システムで扱う主要な変数（在庫、注文量など）を特定。
2. **関係性の言語化**: 「利用可能在庫は、総在庫から予約済み在庫を引いたもの」といった法則を記述。
3. **Grounding Map作成**: 法則と観測（ログ、メトリクス）/テストの対応付けを行う。

### Phase 1: 法則の論理式化
自然言語の法則を厳密な論理式に変換します。
- 例：`∀t. available(t) = total(t) - reserved(t)`
- 普遍量化子（∀）や存在量化子（∃）を用いて適用範囲を明確化します。

### Phase 2: 型による法則の具現化
1. **不可能な状態の排除**: 無効な値を型レベルで表現不可能にします（Brand型など）。
2. **スマートコンストラクタ**: オブジェクト生成時に不変条件を強制し、不正な生成を防ぎます。
3. **Grounded Newtype**: 型にデータの由来（SourceOfTruth）と検証方法（Measurement）を紐付けます。

### Phase 3-4: Property-Based TDDサイクル
1. **RED (Phase 3)**: 法則を具体的な値ではなく「性質」としてテスト記述します（Property-based testing）。
2. **GREEN (Phase 4)**: 最小限の実装でテストを通し、型制約を活用して不正状態を排除します。

### Phase 5: 代数的法則の証明
システムの操作が満たす代数的性質（結合律、単位元、可換性など）を特定し、検証します。これにより、並行処理や分散システムでの安全性が数学的に保証されます。

### Phase 6: 多重表象（Multi-Representation）
同一の法則をREST API, GraphQL, CLI, UIなど異なるインターフェースで一貫して提供します。表現形式が変わっても、核となる法則（コアロジック）は不変であることを保証します。

### Phase 7: 実践的法則実装と監視
- **契約プログラミング**: 関数のpre/post条件や不変条件を実装・検証します。
- **Law Telemetry**: 法則の適用回数、違反率、レイテンシなどを監視し、`law.<domain>.<name>.violated` などの形式で計測します。
- **制約伝播**: 法則変更時の影響範囲を自動分析できるようにします。

## 🌟 トラック別実装ガイド

### 🚀 Simple Track
- **アプローチ**: 軽量。YAGNIスコア $\ge 0.9$。
- **ツール**: Zod, Joi, Yupなどのスキーマバリデーション。
- **実装**: Either型によるエラー処理、基本的なバリデーション合成。

### ⚖️ Standard Track
- **アプローチ**: バランス型。YAGNIスコア $\ge 0.8$。
- **ツール**: fp-ts, fast-check, utility-types。
- **実装**: 不変データ構造、ドメイン不変条件の自動検証、状態遷移の関数合成、Property-based testing導入。

### 🔬 Complex Track
- **アプローチ**: 厳密。YAGNIスコア $\ge 0.6$（複雑性を許容）。
- **ツール**: 形式仕様記述（TLA+, Alloy）、数学的検証。
- **実装**: 厳密なドメイン境界管理、制約伝播ネットワーク、全5層の統合適用。

## 🧩 実装パターン (Reference)

LDEをコードに落とし込む際の標準パターンです。

### 1. Grounded Type (型による接地)

```typescript
// Phase 2: 型定義
import { Brand } from 'utility-types';
import { either } from 'fp-ts';

// ソース(UI入力)と検証(zod)を紐付けた型
type Email = Brand<string, "Email">;
const Email = (input: string): either.Either<Error, Email> => {
  return isValidEmail(input) 
    ? either.right(input as Email)
    : either.left(new Error("Invalid Email")); // 法則違反
};
```

### 2. Law as Function (法則の関数化)

```typescript
// Phase 1 & 4: 法則の実装
// Law: "利用可能在庫 = 総在庫 - 予約済"
const calculateAvailable = (total: Stock, reserved: Reserved): Available => {
  // 純粋関数として実装
  return (total - reserved) as Available; 
};
```

### 3. Law Telemetry (観測による接地)

```typescript
// Phase 7: 実行時監視
const reserveStock = (qty: Quantity) => {
  const available = calculateAvailable(total, reserved);
  
  // Pre-condition check
  if (qty > available) {
    // 構造化ログによるGrounding
    logger.warn({
      event: 'law.inventory.availability.violated', // 命名規約準拠
      context: { qty, available },
      violation: 'Order quantity exceeds availability'
    });
    return left(new InsufficientStockError());
  }
  // ...
};
```

### 4. Property Test (性質テスト)

```typescript
// Phase 3: Property-based Testing
test('Available stock invariant', () => {
  fc.assert(
    fc.property(fc.nat(), fc.nat(), (total, reserved) => {
      // 前提: 予約は総在庫を超えない
      if (reserved > total) return true; 
      
      const available = calculateAvailable(total, reserved);
      // 法則: available + reserved = total (保存則)
      return available + reserved === total;
    })
  );
});
```

## ⚠️ 導入の注意点
*   **段階的導入**: まずSimple Trackから始め、必要に応じて厳密性を高める。
*   **過接地回避**: 観測粒度はトラックに応じて調整し、パフォーマンスへの影響を抑える。
*   **チーム理解**: 理論よりも実践的価値（バグ削減、変更容易性）を共有する。
