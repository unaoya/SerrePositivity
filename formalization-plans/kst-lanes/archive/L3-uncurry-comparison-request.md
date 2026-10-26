# Ind-S (9) 可逆比較の利用側：uncurry の関手同型保存

採用済みの厳密切断撤回に伴う、F1 正本への補助補題の依頼。
新しい存在境界・一般 BF 整流は導入しない。

現利用側の厳密式への依存：
- `ZeroMiddleReconstructedFamily.lean:74` は encode/read の厳密切断で点を回収する。
- `ZeroMiddleReconstructedDiagonal.lean:51` はその回収で encode(ℓ) の対角を厳密同定する。
- `VerdierNormalizedSharedDiagonal.lean:84` は上記の等式で上下の全共有対角を貼る。
- `ZeroMiddleNormalizedFamily.lean:37`・`:47` の厳密読出し保存・冪等性も旧強仕様に依存する。
これらは旧強仕様に条件付きで保持するが、実供給は要求しない。

新仕様では正規化上側の対角から、直接 path 評価の全族可逆比較に沿って元へ戻す。
`ZeroMiddleLongFamilyComparison` は固定合成端の fiber 内の比較を全長 Hom 族と
直接 path の全族の関手同型へ写す。次に標準区間像へ渡すため、下記の汎用補題を使いたい。
既存の公開名があればその指定でよい。証明は K-B に重ねない。

```lean
import SerrePositivity.InfinityCategories.Core.Equivalence
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
universe u
-- 求める型（全族の可逆比較。点ごとの同型ではない）
∀ (A B X : SSet.{u}) [Quasicategory X]
  (f g : B ⟶ (ihom A).obj X),
  FunctorIso f g → Nonempty (FunctorIso (uncurry f) (uncurry g))
```

K-B の適用は A=Δ[1]、X=SpaceInfinity、B=元の同じパラメータ K。
実長 Hom の直接評価を `coherentHomIntervalComparison` と固定境界 fiber の包含へ
後合成した二つの実写像が f・g である。同じ K の非退化一単体を保持するため、
各 K 頂点での比較では代用できない。型検査用コピーは `/tmp/kb-uncurry-comparison-request.lean`。

この補題だけで c4 全体の完了は主張しない。指定有限端点・二短辺と両立する移送と
元の上下二胞体との照合が残る。厳密切断自体の再要求ではない。

## 既存 API による利用側の解消

この利用側では追加供給は不要。既存の
`F2.Presentable.functorIsoTensor` で直接 path 全族の比較と区間恒等を直積にし、
`intervalMappingUncurry (coherentHomIntervalComparison _ _)` へ後合成できる。
`ZeroMiddleSuppliedReconstruction.diagonalIso` は正規化対角の厳密回収とこの全族比較を接続する。
厳密切断は使わない。依頼解消はユーザー経由で中継する。
