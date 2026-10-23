module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.HornBoundaryHomPullbacks
public import SerrePositivity.InfinityCategories.F1.Cocartesian.RestrictionDiagramMaps

/-!
概要：元の境界 Hom の pullback 表示を、同じ反変 Hom 図式の射で書く。
方針：元の直接制限と図式の map の等式で四射を揃える。
規約：元の境界・面・ホーン・共有境界を保持する。
使われ方：厳密 cospan 比較を実際の境界 Hom へ戻す。
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

/-- 分類先の宇宙を明示した、元の native core の同じ反変図式。 -/
def cocartesianPullbackNativeLiftCoreFunctor
    {E F : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q] :
    (Over B)ᵒᵖ ⥤ SSet.{u + 1} :=
  cocartesianPullbackNativeCoreFunctor p q ⋙ SSet.uliftFunctor.{u + 1, u}

/-- 同じ分類先の宇宙を明示した、元の区間 Hom の反変図式。 -/
def intervalDiagramLiftOverFunctor {X : SSet.{u + 1}}
    (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X) : (Over B)ᵒᵖ ⥤ SSet.{u + 1} :=
  (uliftOverFunctor.{u, u + 1} B).op ⋙ intervalDiagramOverFunctor P Q

/-- 元の native 境界 Hom は、同じ反変図式の四射の厳密な pullback。 -/
lemma cocartesianHornBoundary_nativeDiagram_isPullback
    {E F : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q] :
    IsPullback
      (((cocartesianPullbackNativeCoreFunctor p q) ⋙ SSet.uliftFunctor.{u + 1, u}).map
        (HornBoundaryOver.faceInclusion n i σ).op)
      (((cocartesianPullbackNativeCoreFunctor p q) ⋙ SSet.uliftFunctor.{u + 1, u}).map
        (HornBoundaryOver.hornInclusion n i σ).op)
      (((cocartesianPullbackNativeCoreFunctor p q) ⋙ SSet.uliftFunctor.{u + 1, u}).map
        (HornBoundaryOver.toFace n i σ).op)
      (((cocartesianPullbackNativeCoreFunctor p q) ⋙ SSet.uliftFunctor.{u + 1, u}).map
        (HornBoundaryOver.toHorn n i σ).op) := by
  simpa only [cocartesianPullbackNativeLiftPre_eq_diagramMap] using
    (cocartesianHornBoundary_native_isPullback n i σ p q)

/-- 同じ分類先の境界 Hom も、持ち上げた反変図式の四射の厳密な pullback。 -/
lemma cocartesianHornBoundary_targetDiagram_isPullback
    {X : SSet.{u + 1}} (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X) :
    IsPullback
      (((uliftOverFunctor B).op ⋙ intervalDiagramOverFunctor P Q).map
        (HornBoundaryOver.faceInclusion n i σ).op)
      (((uliftOverFunctor B).op ⋙ intervalDiagramOverFunctor P Q).map
        (HornBoundaryOver.hornInclusion n i σ).op)
      (((uliftOverFunctor B).op ⋙ intervalDiagramOverFunctor P Q).map
        (HornBoundaryOver.toFace n i σ).op)
      (((uliftOverFunctor B).op ⋙ intervalDiagramOverFunctor P Q).map
        (HornBoundaryOver.toHorn n i σ).op) := by
  simpa only [intervalDiagramOverPre_ulift_eq_diagramMap] using
    (cocartesianHornBoundary_interval_isPullback n i σ P Q)

end SerrePositivity.InfinityCategories
