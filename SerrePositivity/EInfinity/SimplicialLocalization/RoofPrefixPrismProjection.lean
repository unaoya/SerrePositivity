module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentRightConeFront

/-!
# 元の native roof 全 prism の底は標準評価円柱

概要：元の slice prism の前面を評価自然変換の元の全円柱へ同定する。
方針：全 coherent 前面と同じ nerve 自然変換円柱を全単体で照合する。
規約：元の時間・図式・Kan 源関手・局所化射を保持する。
使われ方：native roof 全三角形の元の左脚。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma simplex_front {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    (kanHammockNerve C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op (simplex C U p hp σ hU Γ t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (KanHammockCategory C)).app (Opposite.op ⦋n⦌)
        (frontDiagram C U p Γ t) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagram_front (frontDiagram C U p Γ t)
    ((kanHammockSourceFunctor C).obj Y) (lastHom C U p hp σ hU Γ t)
    (lastHom_comp C U p hp σ hU Γ t)

lemma prism_projection : prism C U p hp σ hU ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj Y))) =
    (β_ (Δ[1] : SSet.{u}) (nerve I)).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy p).h ≫
      hammockLocalizationNerveMap C := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, Γ⟩
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    SSet.yonedaEquiv.symm (simplex C U p hp σ hU Γ (stdSimplex.objEquiv t).toOrderHom)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply,
    simplex_front C U p hp σ hU Γ (stdSimplex.objEquiv t).toOrderHom]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (KanHammockCategory C)).app (Opposite.op ⦋n⦌)
    (frontDiagram C U p Γ (stdSimplex.objEquiv t).toOrderHom) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (KanHammockCategory C)).app (Opposite.op ⦋n⦌)
      (((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy p).h.app (Opposite.op ⦋n⦌) (Γ, t)) ⋙
        kanHammockSourceFunctor C)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveNatTransHomotopy_app]
  rfl

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
