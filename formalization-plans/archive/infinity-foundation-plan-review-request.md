# レビュー依頼：∞ 圏基盤の整備計画（2026-10-28）

あなたには、Lean 4 プロジェクト SerrePositivity のリファクタ計画をレビューしていただきます。

## 前提と制約

- リポジトリ：`/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity`（ブランチ main。計画の数値は HEAD `cbb891432`〜`bf573b627` の時点のもの。計画文書は未コミットです）。
- **読み取りのみ**です。`.lean` ファイル、計画文書、git の状態は変更しないでください。ビルド（`lake build`）も不要です。
  一時ファイルが必要なら `/tmp` の下に作ってください。
- 同じワークスペースで、別のセッション（KST の各レーン、Bhatt–Scholze）が作業しています。作業中のファイルに触れないでください。

## 読む文書

1. **本体**：`formalization-plans/archive/stage-i/infinity-foundation-plan.md`。
2. **根拠**：
   - `formalization-plans/archive/stage-i/refactoring-verdier.md`（Verdier 列の二つの定義、R48〜R57、新しい数学 M1〜M7）
   - `formalization-plans/archive/stage-i/refactoring-infinity-r2.md` §3（R26〜R47・R59〜R67）
   - `formalization-plans/archive/infinity-outside-survey-2026-10-28.md`（∞ 層の外にある一般論）
   - `formalization-plans/archive/repository-survey-2026-10-28.md`（全体の地図）
3. **運用の前提**：`formalization-plans/archive/stage-i/refactoring-infinity.md` の §2（不変条件）と §8（第 1 窓の分担）。`scripts/move_module.py` と `scripts/refactor/verify.sh` が何をするか。

計画の要旨：

- `SerrePositivity/InfinityCategories`（quasicategory 模型。`X : SSet` に `[Quasicategory X]` を付けて ∞ 圏とする）を、KST・DifferentialGraded・EInfinity に依存しない自立したライブラリにする。
- 外にある一般論（約 2,800 本）を取り込み、ルートのビルドに完成品をすべて含める。
- 最終的には、安定 ∞ 圏の Verdier 商を一般に構成する。
- 段 A〜G に分け、公開名・型・数学的内容を変えずに移動と分割を行う。止めずにできる準備（W0）、短い全停止（W1）、領域ごとの順次停止（W2）の三つの窓で進める。

## 見てほしい観点

1. **数学的に妥当か**
   - §3 の層の順序 `Simplicial < Core < Kan < Coherent < {F1, F1B, HomotopyLimits} < Stable < F2 < StablePresentable < {DGNerve, DoldKanComparison} < Derived` が、∞ 圏論の標準的な依存関係（Kerodon・HTT・HA）と合っているか。
   - Kan 複体の層を quasicategory の層（Core）の上に置く判断（§3。社内レビューで Kan < Core から改めた）と、Kan と Core の境目の決め方は適切か。
   - Verdier 列の正本を「9 人論文の定義（充満忠実・核と像が一致・cofiber 辺での DK 局所化）」にする判断（R50）は妥当か。
   - 段 G の M1〜M7 で、Verdier 商の構成に足りないものはないか。
2. **コードの事実と合っているか**
   - 計画が挙げるパス・宣言名・件数を、少なくとも 10 個、実物で確かめてください。
   - 優先して確かめてほしいもの：
     - 段 B の R48・R49a が層を破らないという主張と、§4 の「中核の閉包に入り込む辺」の一覧に漏れがないか。
     - `F2.lean` とルートの入口の状態。
     - R61 の重複の組。
3. **実行できるか、順序は正しいか**
   - 前提に漏れがないか。段の順序に隠れた循環がないか。工数の見積りに大きな外れがないか。
   - 特に R64・R66・R71・R50・R56 と、§6 の窓の分け方（W0・W1・W2）を見てください。
   - 窓の長さが現実的か。窓の外で新しいファイルを足すだけで先行できる部分はないか。
4. **読みやすさ**
   - 実施するエージェントが、この文書と出典だけで一つの段を実行できるか。
   - 定義されていない略号（L1・Sp-S1・SC-C3・γ-B など）や、数値の食い違いがないか。

## 前提知識

計画は 10-28 に社内で 3 観点のレビューを受け、改訂済みです（§8 に変更点）。§9 の未決の点について意見があれば、それも書いてください。

## 出力の形式

- 日本語で 2,000 字以内。
- 指摘を「阻害（直さないと実施できない）」「重要」「軽微」の三つに分け、重要度の高い順に並べてください。
- 各指摘には、根拠（ファイル:行、またはコマンドの出力の要点）と、計画の本文をどう直すかの案を付けてください。
- 最後に、全体の評価を 3 行で書いてください。
