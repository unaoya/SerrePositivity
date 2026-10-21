module

public import SerrePositivity.EInfinity.BarrattEccles.SourceFramePostcompose

/-!
# 既存 Map^h と reduced hammock の比較の終域自然性

概要：元の Map^h の終域射の作用を既存の高次比較同型が保つ。
方針：両変数に自然な元の終域比較と同じ frame 比較の因子化を使う。
規約：既存の Map^h・同じ比較同型・元の終域射を保持する。
使われ方：実 DK Hom と既存 Map^h の全自然比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

lemma mappingSpaceReducedHammockComparisonIso_postcompose (X : (operad A).Algebra)
    {Y Z : (operad A).Algebra} (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        (((mappingSpace A).obj (op X)).map g)) ≫
      (mappingSpaceReducedHammockComparisonIso A X Z).hom =
    (mappingSpaceReducedHammockComparisonIso A X Y).hom ≫
      AnodyneHomotopy.anodyneQ.map (algebraReducedHammockPostcompose A X g) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := sourceFrameHomComparison_lift_localized_isIso A X Y
  have h := congrArg Q.map (congrArg SSet.uliftFunctor.{u + 1, u}.map
    (((sourceFrameHomComparison A).app (op X)).naturality g))
  simp only [Functor.map_comp] at h
  apply (cancel_epi (Q.map (SSet.uliftFunctor.{u + 1, u}.map
    (((sourceFrameHomComparison A).app (op X)).app Y)))).mp
  rw [← Category.assoc, ← h, Category.assoc,
    sourceFrameReducedHammockComparison_targetComparison,
    sourceFrameReducedHammockComparison_postcompose,
    ← sourceFrameReducedHammockComparison_targetComparison, Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
