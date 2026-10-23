# R-B：安定・導来 ∞ 圏の整理

## 引き継ぎ

- 現在地：`refactor/r-b`、`../SerrePositivity-B`。基点 main `c6692be81` は checkpoint から計画文書だけが増えている。指定の .lake クローン完了。
  R24 を適用し Stable・Derived・DGNerve 集約ビルド成功（11,358 jobs）。指定3監査と dg nerve 監査も成功。Derived はコード生成の再帰上限を実行オプションで拡張。SemifreeLimits の本文はバイト一致、旧ファイルは削除。
- 残り（依存順）：Stable/KST 4 組、Derived 準重複の直接統合、R3。
  R-A 取り込みの合図後に rebase・.lake 再クローンを行い、2-1〜2-3（Core/F1B への移動）。各項目の所要時間はビルド時間確認後に見積もる。
- 主要宣言：既存名を維持。`isTerminalVertex_semifree_zero`、`isInitialVertex_semifree_zero`、`semifreeFiberSquare`、
  `semifreeFiberSquare_isPullback`、`semifreeFiberSquare_inclusion` の所在は Derived/SemifreeLimits（名前空間 DGNerve を保持）。
- 依存と提供：Core/F1/F1B は R-A 取り込みまで読み取り専用。移動ツール未着につき、手変更を archive/refactor-r-b-manual-files.txt に記録。
- 未コミット：R24 の移動・import 修正・上記記録。検証完了後に項目単位でコミットする。
- 既知の問題：未追跡 DGKernelDerivedMapInvertible はユーザーの個別許可により main 作業ツリーから削除済み。
  DGKernelDerivedQuasiIsoMapInvertible と全非コメントトークンが一致することを削除直前に確認した。
- 次の一手：R24 の項目別コミットを保存し、準備済み KST 4 本の直接削除・置換を適用する。

## 方針

- 正本：refactoring-infinity.md §8 とユーザーの着手順指示。互換シムを残さず直接移動・置換する。
- 数学的内容・宣言の型・証明を維持し、新しい sorry・公理は追加しない。
- R24 は Derived/SemifreeLimits に移動し、DGNerve 集約から削除、Derived 集約に追加。
  DGNerve 名前空間の宣言名を変えず、dg nerve 監査には新所在を明示 import して既存チェックを保持。
- 集約ビルドは並行起動せず、単一コマンドで実行する。項目完了後は指定3監査を通し、承認待ちせず次へ進む。

## 準備済み（まだソースへ適用していない）

- KST 4 本の削除と import/参照の直接置換はユーザーが追加許可済み。Stable 正本を保持する。
  11 宣言すべての型が Lean で定義的に等しい（`/tmp/r-b-kst-typecheck.lean`、成功ログ同名 `.log`）。
  適用用 `/tmp/r-b-kst-dedup.py` は §5 への対応表記入を含む。
- Derived の一般宣言14組はソースの型・証明トークンが名前置換後一致し、Lean で型の定義的同一性も確認済み。
  検証 `/tmp/r-b-derived-generic.py`、型チェック `/tmp/r-b-derived-typecheck.lean`（成功ログ同名 `.log`）。
  `python3 /tmp/r-b-derived-generic.py --apply` は canonical の宣言を DGNerve の新2ファイルへ直接移す予定。
- Prop の証明共有は型維持を条件にユーザー許可済み。新しい2補題の preview は Lean 単体検証成功。
  `/tmp/r-b-proof-cases.py --apply` は4定理の証明だけを共有化し、§5 に新補題の所在を記録する。
- データ構成は本体維持、D レーン再開後判断。指定の archive/refactor-near-duplicates-derived-2026-10-23.md に19組の差分表を保存済み。
- R-A からの move_module.py はまだ存在しない。rebase・再クローンはコーディネータの合図を待つ。
