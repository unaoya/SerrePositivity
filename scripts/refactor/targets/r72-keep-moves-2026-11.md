# R72 keep 側の move：§10.29 静的調査と停止（2026-11-01）

main f2b506a09 の§10.29に従って全候補を調査した。R72の元12本と追加EvaluationFamilyの計13本のうち、現在のkeep側がW2a禁止接頭辞に当たるのは7本。残り6本は既にSimplicialの下にある（BoundaryOneの承認済みmoveを含む）。

7本すべて中核から直接、または純粋なHotAを経由して到達する。非純粋0本・未到達0本。keepのソース宣言は計31件、snapshotは補助宣言込み41件。既存成果物からの採取は13.208秒・終了コード0。

| 元モジュール（HA以下） | keep宣言 | 移し先案（HA.Simplicial以下） |
|---|---:|---|
| Generated.Basic | 2 | GeneratedLeftClass |
| Generated.FunctorClosure | 3 | GeneratedLeftClassFunctor |
| HomotopyFunctionComplex.DiagonalFrame | 6 | DiagonalDiagram |
| HomotopyFunctionComplex.QuillenStandardFrame | 4 | StandardSimplexCosimplicialHom |
| HomotopyFunctionComplex.StandardCosimplicial | 6 | FiniteTensorAdjunction |
| Transfer.EvaluationFamily | 9 | EvaluationMorphismProperties |
| Transfer.FullyFaithfulLifting | 1 | FullyFaithfulLifting |

## 純粋性と到達経路

各宣言のuses_modules・used_constantsを調べた。ModelCategory定数・ModelBridge・Quillenモジュールへの使用は0。非ローカルなプロジェクト依存はResolutionHom、FiniteTensor、NonsingularPresentation、SubcomplexTensorの純粋なHom・余極限構成であり、これらの本文にModelCategory使用はない。EvaluationFamilyのMathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations依存は射のクラスの構造であり、モデル圏の公理を仮定しない。

中核からの経路は、入口と途中のimportを全件保存し、HotAの途中ノードが本文でModelCategoryを使用しないことを確認した（import行・コメント・文字列を除いて確認）。候補自身の純粋性には上記snapshotを使用した。

- `InfinityCategories.F1.Universe.InnerAnodyne` → `HomotopicalAlgebra.Generated.FunctorClosure` → `HomotopicalAlgebra.Generated.Basic`
- `InfinityCategories.F1.Universe.InnerAnodyne` → `HomotopicalAlgebra.Generated.FunctorClosure`
- `InfinityCategories.F1.TwistedArrow.TwistedHomDiagonal` → `HomotopicalAlgebra.Simplicial.DiagonalAdjunction` → `HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame`
- `InfinityCategories.HomotopyLimits.KanTensorFrameAdjunction` → `HomotopicalAlgebra.HomotopyFunctionComplex.QuillenStandardFrame`
- `InfinityCategories.F1.Joins.CosliceTwistedHomEquivalence` → `HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence` → `HomotopicalAlgebra.Simplicial.DiagonalKanTests` → `HomotopicalAlgebra.Simplicial.DiagonalAnodyne` → `HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching` → `HomotopicalAlgebra.Simplicial.DiagonalMatching` → `HomotopicalAlgebra.HomotopyFunctionComplex.StandardCosimplicial`
- `InfinityCategories.HomotopyLimits.KanMonoArrowFactorization` → `HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization` → `HomotopicalAlgebra.Simplicial.Generators` → `HomotopicalAlgebra.Transfer.EvaluationSmallness` → `HomotopicalAlgebra.Transfer.EvaluationFamily`
- `InfinityCategories.F1.Cocartesian.CellAttachmentFibrations` → `HomotopicalAlgebra.Simplicial.UniverseLiftLifting` → `HomotopicalAlgebra.Transfer.FullyFaithfulLifting`

## 一括模擬

7本をmoveし、Generatorsから移動後GeneratedLeftClassへ直接importを補う模擬は、直接違反296→294、禁止閉包W1=1のまま、W2a/W2b=172→166、ratchet増加0。数学ソースへの適用はしていない。EvaluationFamilyは移動後もMathlibのimport行にModelCategoryという語を含むため、既存の語による検出規則では禁止対象に残る。今回その規則は変更しない。

## 停止：同じmoduleへのsplitとmoveを現在のvalidatorが拒否

w2a.jsonには7本中5本がすでにsplitとして登録されている。§10.29どおり同じmoduleのkeep側moveをR72(5)として追記する最小入力（Generated.Basicの既存split＋move案）を、既存snapshotとpre-windows上でvalidateしたところ、次を再現した。

```text
duplicate module: SerrePositivity.HomotopicalAlgebra.Generated.Basic
```

validate_targets.py:78 は同じmoduleの二つ目の項目をアクションによらず拒否する。新たなmoveを先に置いても重複制限は同じであり、split元を移し先へ書き換える表現も「destination is also a source」の制限に当たる。無断でw2a.jsonを不正な形式にせず、既存道具の制約として停止した。

提案：同一moduleについて「splitを1件、そのkeep側をmoveする項目を後続で1件」の組だけを明示的に許可する。模擬・適用はsplit→keep moveの順とし、その他の重複は引き続き拒否する。保持側のmodule写像と移動宣言ごとの写像を両立させる保存比較・試験も必要。

今回のLeanソース変更・ビルド・コミットは0。w2a.jsonは変更していない。7件の候補JSON、全依存モジュール、到達経路、snapshot、模擬結果、validatorの停止は `.lake/verify/batch-w1w2a/stop2/addendum29/` に保存。再ビルド・after snapshot・保存比較・停止点2は未到達。既存のdownstream補充は未コミットのまま保持。

## §10.30 承認後：適用

validatorはsplit→keep moveの組だけを許可するよう拡張し、許す組・拒否する組を含む170件のPython試験に成功（道具9bc69dc79）。7件を加えたw1+w2aの1,285項目はPASS、増加0。上表の移し先が既存ファイルと衝突しないことを確認し、7本を一括move、利用者のimportを更新。新たな利用元11本の元snapshotも、元ソース・依存ソースのハッシュ照合後に保存した。downstream補充を含まないmove単独のコミットを作り、作業木には承認済み補充を保持する。Generatorsの補充・ビルド・保存比較は後続の停止点2に記録する。
