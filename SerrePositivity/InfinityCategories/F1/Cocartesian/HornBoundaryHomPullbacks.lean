module

public import SerrePositivity.InfinityCategories.F1.HornBoundaryOver
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CellAttachmentPullbacks

/-!
概要：同じ標準境界の native Hom と分類先 Hom を、ホーンと残りの面の厳密な pullback にする。
方針：同じ底上の標準四射の pushout に、元の両 Hom の降下を適用する。
規約：境界・ホーンに quasicategory 性を要求せず、元の四つの制限を保持する。
使われ方：境界比較の次元による帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}} (n : ℕ) (i : Fin (n + 2)) (σ : (Δ[n + 1] : SSet.{u}) ⟶ B)

/-- 元の native core の同じ標準境界への制限は、実際のホーンと面の pullback。 -/
lemma cocartesianHornBoundary_native_isPullback
    {E F : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q] :
    IsPullback
      (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.faceInclusion n i σ))
      (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.hornInclusion n i σ))
      (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.toFace n i σ))
      (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.toHorn n i σ)) :=
  cocartesianCellAttachment_nativeLift_isPullback
    (HornBoundaryOver.toFace n i σ) (HornBoundaryOver.toHorn n i σ)
    (HornBoundaryOver.faceInclusion n i σ) (HornBoundaryOver.hornInclusion n i σ)
    (HornBoundaryOver.isPushout n i σ) p q

/-- 分類先の同じ標準境界への区間 Hom 制限も、同じホーンと面の pullback。 -/
lemma cocartesianHornBoundary_interval_isPullback
    {X : SSet.{u + 1}} (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X) :
    IsPullback
      (intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.faceInclusion n i σ)))
      (intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.hornInclusion n i σ)))
      (intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.toFace n i σ)))
      (intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.toHorn n i σ))) :=
  cocartesianCellAttachment_interval_isPullback
    (HornBoundaryOver.toFace n i σ) (HornBoundaryOver.toHorn n i σ)
    (HornBoundaryOver.faceInclusion n i σ) (HornBoundaryOver.hornInclusion n i σ)
    (HornBoundaryOver.isPushout n i σ) P Q

end SerrePositivity.InfinityCategories
