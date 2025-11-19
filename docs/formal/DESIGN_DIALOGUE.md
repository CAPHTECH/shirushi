---
doc_id: SHI-FORMAL-2025-0005
title: 2025-11-19 アーキテクチャ設計レビュー対話ログ
version: "0.1.0"
status: Draft
created_at: 2025-11-19
---

# 2025-11-19 アーキテクチャ設計レビュー対話ログ

本ログは、二役(設計責任者/形式検証責任者)での対話により docs/formal の改訂方針を確定した記録である。各ラウンドで懸念を洗い出し、解を得るまで議論を継続した。

## 参加ロール
- **ロールA (設計責任者)**: CLI/API の機能要求、ユーザー体験、運用制約を担当
- **ロールB (形式検証責任者)**: Alloy/TLA+ モデル、検証計画、CI 連携を担当

## ラウンド1: Assign パッチ適用の原子性
- **A**: 「assign は dry-run/実書き込みの両モードがあるが、現在の TLA+ では単一アクションで抽象化されすぎ。途中でエラーが起きた時に doc/index がズレない保証を明示したい。」
- **B**: 「パッチバッファ変数を導入し、`prepare → commit/discard` の 2 段階アクションに分解する。serialCounter の予約値や requestId も保持すれば、サービス層ログと結びつけられる。」
- **A**: 「dry-run で `docs`/`index` が絶対に変わらないこと、失敗条件が全て discard に落ちることを invariants として追加してください。」
- **B**: 「`PatchAtomicityInvariant` を導入し、commit 時のみ doc/index 更新されるよう TLA+ を修正する。」
- **合意事項**: `patchBuffer` と `ServiceAssignPrepare/Apply/Discard` を追加し、dry-run/失敗分岐を形式化する。

## ラウンド2: Config→形式モデル自動生成
- **A**: 「.shirushi.yml の変更が Alloy/TLA+ に反映されない問題を解消したい。formal-sync ツールを CLI に入れて、CI で自動生成したい。」
- **B**: 「仕様書を `formal/FORMAL_SYNC_SPEC.md` にまとめ、`shirushi formal-sync` コマンドで Alloy/TLA+ 定数断片を生成する計画を明文化する。プレースホルダ完全性や enum の値一致は生成ステップで検証し、結果をモデルに読み込ませる。」
- **A**: 「生成物は git 管理せず、CI と Docker verify から毎回生成＆diff チェックする方針をドキュメント化しよう。」
- **合意事項**: formal-sync の入出力・検証手順を仕様化し、docs/api からの参照と CI 手順を追記する。

## ラウンド3: API/MCP サービス層の形式化
- **A**: 「MCP/CI で CLI と同じ安全性を保証するため、サービス層契約を TLA+ で直接表したい。」
- **B**: 「`serviceLog` 変数と `ServiceLint/ServiceScan/ServiceAssign` アクションを新設し、エラーコードや read-only 契約をシーケンスとして記録する。`ServiceReadOnly`/`ServiceErrorCodesTotal` を新しい安全性特性として証明する。」
- **A**: 「Assign 成功/失敗もサービスログに残し、CI が JSON で結果を引けるように doc に反映する。」
- **合意事項**: サービス層アダプタの形式仕様を TLA+ に追加し、interface/internal design に API 契約を追記する。

## ラウンド4: ストリーミング lint / インクリメンタル検証
- **A**: 「`lint --json --stream` のイベント順序(開始→部分→最終)と exit code の一貫性を検証で保証したい。」
- **B**: 「`activeStream` 変数と `StreamEvents` アクションを導入し、 start/doc/summary イベントをモデル化する。summary の exitCode が serviceLog と一致するかを `StreamFinalConsistent` で監視する。」
- **A**: 「ドキュメントにはイベントスキーマと CLI/MCP の仕様を追記する。」
- **合意事項**: ストリーミングイベントの形式化と設計書追記を実施する。

## ラウンド5: Dimension handler 個別仕様
- **A**: 「enum.selectByPath など個別 handler の前提/結果を Alloy で直接検証できるようにしてほしい。」
- **B**: 「PathPattern にカテゴリ集合を持たせ、`firstMatchingRule` 関数で「最初にマッチしたルールのみ採用」を強制する。`enum_from_doc_type`、`serial` のポスト条件も個別 predicate として追加し、`systemInvariant` に連結する。」
- **A**: 「仕様書の dimension セクションにも handler ごとのルール表を載せよう。」
- **合意事項**: Alloy モデルに handler predicate を追加し、docs に設計意図を反映する。

## 結論
- 5 テーマとも解消済み。未解決事項なし。
- 合意内容に基づき docs/api/*, docs/formal/*, TLA+/Alloy を更新し、Docker verify を通すことを決定。
