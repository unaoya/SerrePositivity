module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.TerminalNativeLeg
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeCoordinates
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyDiagram

/-!
概要：coherent な終頂点付加図式から、指定された native 余錐を回収する。
方針：小さい終頂点付加余錐を同じ全 coherent 図式で後合成する。
規約：strict 性は仮定しない。
使われ方：分解後の strict 余錐の全 native データとホモロジーの照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  (A : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve (WithTerminal J)) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev dgBarExtendedBaseDiagram :=
  (SSet.uliftFunctor.{max (u + 1) v, u}).map
    (nerveMap (WithTerminal.incl : J ⥤ WithTerminal J)) ≫ A

def dgBarExtendedNativeCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (dgBarExtendedBaseDiagram R D A) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalNativeCocone R D (J := J)).val ≫ A, by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalNativeCocone R D (J := J)).property]⟩

lemma dgBarExtendedNativeCocone_vertex :
    (dgBarExtendedNativeCocone R D A).vertex =
      A.app (Opposite.op ⦋0⦌) (ULift.up (nerveEquiv.symm WithTerminal.star)) := by
  change A.app _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalNativeCocone R D (J := J)).vertex = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalNativeCocone, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_vertex]
  rfl

lemma dgBarExtendedNativeCocone_simplex_zero (j : J) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D (dgBarExtendedBaseDiagram R D A)
      (dgBarExtendedNativeCocone R D A) (nerveEquiv.symm j) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex A (ComposableArrows.mk₁ (WithTerminal.homFrom j)) := by
  change SSet.yonedaEquiv
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm (ULift.up (nerveEquiv.symm j))) (𝟙 Δ[0]) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalNativeCocone R D (J := J)).val) ≫ A) = _
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarJoinIntervalIdentity]
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex_natural, SSet.yonedaEquiv_symm_app_id,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalNativeCocone_leg R D j]
  rfl

lemma dgBarExtendedNativeCocone_module :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeModule R D (dgBarExtendedBaseDiagram R D A)
      (dgBarExtendedNativeCocone R D A) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex A (nerveEquiv.symm WithTerminal.star) := by
  change (dgBarExtendedNativeCocone R D A).vertex.obj 0 = _
  rw [dgBarExtendedNativeCocone_vertex]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
