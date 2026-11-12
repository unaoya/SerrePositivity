module

public import SerrePositivity.EInfinity.Hammock.ContravariantThomasonArrows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ContravariantGrothendieckComponents

/-!
# 任意の右ラベルを固定した元の反変対角射列

概要：元の左ラベルの対角を反変 Grothendieck 全圏の元の射列へ送る。
方針：一般化した左成分の単位・合成則を元の二成分の射の判定へ渡す。
規約：元の全射と右集合ラベルを保持し、右に圏値の構造を要求しない。
使われ方：DK9.5の重み付き左比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ContravariantThomason
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ Cat.{u, u}) (S : W ⥤ Type u)
  {n : ℕ} (e : ComposableArrows (labels F S n) n)

def vertex (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F :=
  op ⟨op (e.obj i).base, op ((e.obj i).left.obj i)⟩

def arrow {i j : Fin (n + 1)} (h : i ⟶ j) : vertex F S e i ⟶ vertex F S e j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ContravariantGrothendieckComponents.homMk (e.map h).base (leftArrow F S e h)

def simplex : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F) n where
  obj := vertex F S e
  map := arrow F S e
  map_id i := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ContravariantGrothendieckComponents.hom_ext_heq _ _ ?_ ?_
    · change (e.map (𝟙 i)).base = 𝟙 _
      rw [e.map_id]
      rfl
    · exact (leftArrow_id_heq F S e i).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ContravariantGrothendieckComponents.fiberMap_id_heq (vertex F S e i)).symm
  map_comp h l := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ContravariantGrothendieckComponents.hom_ext_heq _ _ ?_ ?_
    · change (e.map (h ≫ l)).base = (e.map h).base ≫ (e.map l).base
      rw [e.map_comp]
      rfl
    · exact (leftArrow_comp_heq F S e h l).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ContravariantGrothendieckComponents.fiberMap_comp_heq (arrow F S e h) (arrow F S e l)).symm

lemma simplex_projection :
    simplex F S e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F =
      e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.projection _ _ := rfl

lemma simplex_operator {m : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    simplex F S ((SimplexCategory.toCat.map θ).toFunctor ⋙ e ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map ((F ⋙ nerveFunctor).flip.map θ.op) (𝟙 S)) =
      (SimplexCategory.toCat.map θ).toFunctor ⋙ simplex F S e := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma simplex_labels {T : W ⥤ Type u} (β : S ⟶ T) :
    simplex F S e = simplex F T (e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map (𝟙 _) β) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.EInfinity.Hammock.ContravariantThomason
