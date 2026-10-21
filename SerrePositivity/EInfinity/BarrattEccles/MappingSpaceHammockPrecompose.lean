module

public import SerrePositivity.EInfinity.BarrattEccles.SourceFramePrecompose

/-!
# 既存 Map^h と reduced hammock の比較の始域自然性

概要：元の Map^h の任意の始域射の作用を既存の高次比較同型が保つ。
方針：元の source frame 比較の同じ因子化と全自然性を使う。
規約：元の Map^h・比較同型・始域射を保持する。
使われ方：実 DK Hom と既存 Map^h の全自然比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

lemma mappingSpaceReducedHammockComparisonIso_precompose (Y : (operad A).Algebra)
    {X' X : (operad A).Algebra} (f : X' ⟶ X) :
    AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        (((mappingSpace A).map f.op).app Y)) ≫
      (mappingSpaceReducedHammockComparisonIso A X' Y).hom =
    (mappingSpaceReducedHammockComparisonIso A X Y).hom ≫
      AnodyneHomotopy.anodyneQ.map (algebraReducedHammockPrecompose A Y f) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := sourceFrameHomComparison_lift_localized_isIso A X Y
  have h := congrArg Q.map (congrArg SSet.uliftFunctor.{u + 1, u}.map
    (NatTrans.congr_app ((sourceFrameHomComparison A).naturality f.op) Y))
  change Q.map (SSet.uliftFunctor.{u + 1, u}.map
      ((((sourceFrameHom A).map f.op).app Y) ≫
        (((sourceFrameHomComparison A).app (op X')).app Y))) =
    Q.map (SSet.uliftFunctor.{u + 1, u}.map
      ((((sourceFrameHomComparison A).app (op X)).app Y) ≫
        (((mappingSpace A).map f.op).app Y))) at h
  simp only [Functor.map_comp] at h
  apply (cancel_epi (Q.map (SSet.uliftFunctor.{u + 1, u}.map
    (((sourceFrameHomComparison A).app (op X)).app Y)))).mp
  rw [← Category.assoc, ← h, Category.assoc,
    sourceFrameReducedHammockComparison_targetComparison,
    sourceFrameReducedHammockComparison_precompose,
    ← sourceFrameReducedHammockComparison_targetComparison, Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
