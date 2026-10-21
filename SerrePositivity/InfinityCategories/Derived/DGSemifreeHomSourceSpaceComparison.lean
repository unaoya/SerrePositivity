module
public import SerrePositivity.InfinityCategories.Derived.DGHomSourceOppositeComparison
public import SerrePositivity.InfinityCategories.Derived.DGCosliceYonedaIsoNaturality
public import SerrePositivity.InfinityCategories.Derived.DGCosliceYonedaOppositeComparison
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomSpaceComparison
/-!
概要：実反対 ∞ 圏上の D(R) 値 Hom を元の F1 表現可能前層と比較する。
方針：全 cochain 上の反対比較、同じ coslice の底同型、右 slice の反転を接続する。
規約：元の全 Hom と同じ augmentation の全関手比較を使う。
使われ方：反変 Hom の全高次関手性と二変数 Hom の統合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- dg 反対圏の一般 Hom 構成は元の固定終域 Hom 関手そのもの。 -/
lemma dgHomTargetUnderlyingSpaceInfinity_semifree_opposite (Q : SemifreeDGModules R D) :
    dgHomTargetUnderlyingSpaceInfinity R (SemifreeDGModules R D)ᵒᵖ (Opposite.op Q) =
      (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgSemifreeHomSourceModuleInfinity R D Q) ≫ dgHomUnderlyingSpaceInfinity R D := by
  unfold dgHomTargetUnderlyingSpaceInfinity dgHomTargetModuleLift
  rw [dgHomTargetModuleDG_opposite]
  rfl
/-- 実反対 ∞ 圏上の全 Hom の基礎空間関手は元の F1 表現可能前層と同型。 -/
def dgSemifreeHomContravariantF1SpaceIso (Q : SemifreeDGModules R D) :
    FunctorIso (dgSemifreeHomContravariantSpaceInfinity R D Q)
      (representablePresheafInfinity (dgSemifreeHomVertex R D Q)) := by
  let C := SemifreeDGModules R D
  let X := dgModuleDerivedInfinityCategory R D
  let x := dgSemifreeHomVertex R D Q
  let e := dgNerveOppositeIso R C
  have h1 := (dgHomTargetSpaceComparisonIso R Cᵒᵖ (Opposite.op Q)).precomp
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map e.hom)
  have h2 := dgCosliceYonedaSpaceIsoNaturality e (SSet.opObjEquiv.symm x)
  rw [dgNerveOppositeIso_hom_vertex] at h2
  have h3 := dgOppositeCosliceYonedaSpaceIso X x
  have H := h1 ≪≫ h2.symm ≪≫ h3
  dsimp only [C, X, x, e] at H
  simpa only [dgHomTargetUnderlyingSpaceInfinity_semifree_opposite,
    dgSemifreeHomContravariantSpaceInfinity, dgSemifreeHomContravariantModuleInfinity,
    Functor.map_comp, Category.assoc] using! H
/-- 実 D(R) 値反変 Hom の基礎空間関手は元の F1 表現可能前層と同型。 -/
def dgSemifreeDerivedHomContravariantF1SpaceIso (Q : SemifreeDGModules R D) :
    FunctorIso (dgSemifreeDerivedHomContravariantSpaceInfinity R D Q)
      (representablePresheafInfinity (dgSemifreeHomVertex R D Q)) :=
  dgSemifreeDerivedHomContravariantSpaceIso R D Q ≪≫ dgSemifreeHomContravariantF1SpaceIso R D Q
end SerrePositivity.InfinityCategories
