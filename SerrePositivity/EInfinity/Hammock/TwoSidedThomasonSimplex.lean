module

public import SerrePositivity.EInfinity.Hammock.TwoSidedThomasonArrows

/-!
# 元の二方向 bar の各単体から全圏の射列への比較

概要：元の対角頂点と三成分の射から元の全圏の関手を構成する。
方針：元の左右の単位・合成計算を三成分の射の判定へ渡す。
規約：元の全頂点・全射・端点移送を保持する。
使われ方：DK9.5の単体的比較射。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedThomason
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

def simplex {n : ℕ} (e : ComposableArrows (labels F G n) n) :
    ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G) n where
  obj := vertex F G e
  map := arrow F G e
  map_id i := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq _ _ ?_ ?_ ?_
    · change (e.map (𝟙 i)).base = 𝟙 _
      rw [e.map_id]
      rfl
    · exact (leftArrow_id_heq F G e i).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.leftMap_id_heq (vertex F G e i)).symm
    · exact (rightArrow_id_heq F G e i).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.rightMap_id_heq (vertex F G e i)).symm
  map_comp h l := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq _ _ ?_ ?_ ?_
    · change (e.map (h ≫ l)).base = (e.map h).base ≫ (e.map l).base
      rw [e.map_comp]
      rfl
    · exact (leftArrow_comp_heq F G e h l).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.leftMap_comp_heq (arrow F G e h) (arrow F G e l)).symm
    · exact (rightArrow_comp_heq F G e h l).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.rightMap_comp_heq (arrow F G e h) (arrow F G e l)).symm

lemma simplex_projection {n : ℕ} (e : ComposableArrows (labels F G n) n) :
    simplex F G e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.projection = e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.projection _ _ := rfl

lemma simplex_operator {n m : ℕ} (e : ComposableArrows (labels F G n) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    simplex F G ((SimplexCategory.toCat.map θ).toFunctor ⋙ e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map
        ((F ⋙ nerveFunctor).flip.map θ.op) ((G ⋙ nerveFunctor).flip.map θ.op)) =
      (SimplexCategory.toCat.map θ).toFunctor ⋙ simplex F G e := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.EInfinity.Hammock.TwoSidedThomason
