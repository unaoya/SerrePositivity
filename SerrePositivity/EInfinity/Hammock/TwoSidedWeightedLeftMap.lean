module

public import SerrePositivity.EInfinity.Hammock.ContravariantThomasonSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel

/-!
# 右ラベル次数を固定した元の重み付き左比較

概要：元の反変対角射列に同じ右集合ラベルを付け、元の混合全圏の nerve へ送る。
方針：既存の左計算と右ラベルの元の等式を使い、全作用素・右ラベルの射に両立させる。
規約：元の重み付き左比較を構成するだけで、弱同値性は後続。
使われ方：DK9.5の既存の一方向 Thomason 定理による証明。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeft
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u}) (S : W ⥤ Type u)

abbrev space : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space (F ⋙ nerveFunctor) (S ⋙ Functor.const SimplexCategoryᵒᵖ)

def simplex {n : ℕ} (e : ComposableArrows (ContravariantThomason.labels F S n) n) :
    ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.mixed F S) n where
  obj i := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F ⋙ S).elementsMk
    ((ContravariantThomason.simplex F S e).obj i) (e.obj i).right
  map h := Functor.Elements.homMk ((ContravariantThomason.simplex F S e).map h) (e.map h).right
  map_id i := Functor.Elements.hom_ext ((ContravariantThomason.simplex F S e).map_id i)
  map_comp h l := Functor.Elements.hom_ext ((ContravariantThomason.simplex F S e).map_comp h l)

lemma simplex_operator {n m : ℕ} (e : ComposableArrows (ContravariantThomason.labels F S n) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    simplex F S ((SimplexCategory.toCat.map θ).toFunctor ⋙ e ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map ((F ⋙ nerveFunctor).flip.map θ.op) (𝟙 S)) =
      (SimplexCategory.toCat.map θ).toFunctor ⋙ simplex F S e := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

def map : space F S ⟶ nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.mixed F S) where
  app _ := ↾fun e => simplex F S e
  naturality {n m} θ := by ext e; exact simplex_operator F S e θ.unop

lemma simplex_labels {T : W ⥤ Type u} (β : S ⟶ T) {n : ℕ}
    (e : ComposableArrows (ContravariantThomason.labels F S n) n) :
    simplex F S e ⋙
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F) β).mapElements =
      simplex F T (e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map (𝟙 _) β) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma map_labels {T : W ⥤ Type u} (β : S ⟶ T) :
    map F S ≫ nerveMap
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F) β).mapElements =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.map (𝟙 (F ⋙ nerveFunctor))
          (Functor.whiskerRight β (Functor.const SimplexCategoryᵒᵖ)) ≫ map F T := by
  ext n e
  exact simplex_labels F S β e

end SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeft
