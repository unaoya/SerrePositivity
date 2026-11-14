module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGHomSourceOppositeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGCosliceYonedaIsoNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGCosliceYonedaOppositeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeHomSpaceComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- dg 反対圏の一般 Hom 構成は元の固定終域 Hom 関手そのもの。 -/
lemma dgHomTargetUnderlyingSpaceInfinity_semifree_opposite (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (Opposite.op Q) =
      (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleInfinity R D Q) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG_opposite]
  rfl
/-- 実反対 ∞ 圏上の全 Hom の基礎空間関手は元の F1 表現可能前層と同型。 -/
def dgSemifreeHomContravariantF1SpaceIso (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomContravariantSpaceInfinity R D Q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D Q)) := by
  let C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D
  let X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D
  let x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D Q
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R C
  have h1 := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetSpaceComparisonIso R Cᵒᵖ (Opposite.op Q)).precomp
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map e.hom)
  have h2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaSpaceIsoNaturality e (SSet.opObjEquiv.symm x)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_hom_vertex] at h2
  have h3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOppositeCosliceYonedaSpaceIso X x
  have H := h1 ≪≫ h2.symm ≪≫ h3
  dsimp only [C, X, x, e] at H
  simpa only [dgHomTargetUnderlyingSpaceInfinity_semifree_opposite,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomContravariantSpaceInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomContravariantModuleInfinity,
    Functor.map_comp, Category.assoc] using! H
/-- 実 D(R) 値反変 Hom の基礎空間関手は元の F1 表現可能前層と同型。 -/
def dgSemifreeDerivedHomContravariantF1SpaceIso (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantSpaceInfinity R D Q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D Q)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantSpaceIso R D Q ≪≫ dgSemifreeHomContravariantF1SpaceIso R D Q
end SerrePositivity.InfinityCategories.Project.DerivedCategories
