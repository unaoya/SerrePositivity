module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomasonNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBarBaseChange

/-!
# 元の二方向 nerve 比較の底の関手への自然性

概要：元の底の全射を関手で送る比較は、元の二方向 bar の比較射と厳密に可換。
方針：同じ単体の底と左右の対角頂点・全射を照合する。
規約：底の弱同値性や逆の選択を仮定しない。
使われ方：DK9.5と10.5の元の比較射の正方形。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason
open _root_.CategoryTheory _root_.Opposite

variable {V W : Type u} [Category.{u} V] [Category.{u} W]
  (H : V ⥤ W) (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

lemma simplex_baseChange {n : ℕ} (e : ComposableArrows (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.labels (H.op ⋙ F) (H ⋙ G) n) n) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.simplex (H.op ⋙ F) (H ⋙ G) e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.baseChange H F G =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.simplex F G (e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pre H
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values F n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n)) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma map_baseChange :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.map (H.op ⋙ F) (H ⋙ G) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.baseChange H F G) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBarBaseChange.baseChange H (F ⋙ nerveFunctor) (G ⋙ nerveFunctor) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.map F G := by
  ext n e
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.simplex_baseChange H F G e

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason
