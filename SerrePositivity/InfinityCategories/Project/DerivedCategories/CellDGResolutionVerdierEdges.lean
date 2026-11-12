module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientLocalizingEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberEdgesFullyFaithful
/-!
概要：cell 増大の実 nerve は分解上の Verdier 辺を元の Verdier 辺へ送る。
方針：完全充満忠実関手による実安定閉包の比較と指定対象像の厳密一致を使う。
規約：全実辺の条件。使われ方：平坦分解後の商の全局所化普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
omit [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 分解上の指定実頂点の増大像は、元の指定実頂点全体と一致する。 -/
lemma dgCellAugmentation_nullVertex_image (P : Set D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D)).app (Opposite.op ⦋0⦌) ''
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation A D).obj x, hx,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    let a : DGCategoryCellResolution.Source A D := ⟨x⟩
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex a, ⟨a, hx, rfl⟩, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ a⟩
/-- 増大の実 nerve による、全実 Verdier 辺の所属の保存・反映。 -/
lemma dgCellAugmentation_verdierEdge_iff (P : Set D)
    (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGCategoryCellResolution.Source A D)) _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D)).app (Opposite.op ⦋1⦌) a ∈
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ↔ a ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A (DGCategoryCellResolution.Source A D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A (DGCategoryCellResolution.Source A D)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A D
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor E :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellAugmentationNerve_isQCatEquivalence A D)
  have hh := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_map_iff E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellAugmentationNerve_isQCatEquivalence A D).isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)
  rw [dgCellAugmentation_nullVertex_image A D P] at hh
  exact hh
/-- 元の実 Verdier 辺を反転する任意関手は、増大への制限で分解上の実 Verdier 辺を反転。 -/
lemma dgCellAugmentation_precomp_inverts (P : Set D) {Y : SSet.{max u v}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D) ≫ F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A (DGCategoryCellResolution.Source A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P)) := by
  intro a ha
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D)
  have hb := hF ((dgCellAugmentation_verdierEdge_iff A D P a).mpr ha)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (E.app (Opposite.op ⦋1⦌) a)).map ((truncation 2).map F))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a).map ((truncation 2).map (E ≫ F))) rfl).mp hb
end SerrePositivity.InfinityCategories.Project.DerivedCategories
