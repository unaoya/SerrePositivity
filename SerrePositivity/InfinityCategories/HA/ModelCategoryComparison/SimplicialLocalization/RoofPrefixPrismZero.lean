module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentRightConeStrict
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalCoconeSimplex

/-!
# 元の混合 coherent 単体の零端は通常の右余錐

概要：時刻零の全単体を元の通常右余錐の coherent 表示へ同定する。
方針：全前面と最後 Hom の通常射の定値公式を使う。
規約：同じ元の右脚を持つ余錐を保持する。
使われ方：native roof prism の零端条件 hb。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

def rightCocone : Cocone (U ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).mapCocone (Cocone.mk Y σ)

lemma simplex_zero {n : ℕ} (Γ : Fin (n + 1) ⥤ I) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.simplex C U p hp σ hU Γ (OrderHom.const _ 0) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C)).app (Opposite.op ⦋n + 1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.rightCocone C U σ) Γ) := by
  let c := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.rightCocone C U σ
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram c Γ
  have hc (i : Fin (n + 1)) :
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram C U p Γ (OrderHom.const _ 0)).obj i = G.obj i.castSucc :=
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_obj_zero C U p Γ (OrderHom.const _ 0) i rfl).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast c Γ i).symm
  have hy : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y = G.obj (Fin.last (n + 1)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_last c Γ).symm
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagram_eq_order
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram C U p Γ (OrderHom.const _ 0)) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom C U p hp σ hU Γ (OrderHom.const _ 0))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom_comp C U p hp σ hU Γ (OrderHom.const _ 0)) G hc hy
  · intro i j hij
    exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_map_zero_zero C U p Γ (OrderHom.const _ 0) i j hij rfl rfl).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_cast c Γ i j hij).symm
  · intro i
    have hd := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast c Γ i).symm
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom C U p hp σ hU Γ (OrderHom.const _ 0) i ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom
            (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_obj_zero C U p Γ (OrderHom.const _ 0) i rfl)
            (rfl : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y = _))) ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom hd hy) := by
        simp only [Category.assoc, eqToHom_trans]
      _ = _ := by
        rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom_zero C U p hp σ hU Γ (OrderHom.const _ 0) i rfl,
          _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.pathMap_zero C U p hp σ hU Γ i, Category.assoc]
        exact congrArg (fun f => toUnit _ ≫ f)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitHom_transport hd hy
            ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map (σ.app (Γ.obj i)))
            (G.map (homOfLE (Fin.le_last i.castSucc)))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_last c Γ i).symm)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix
