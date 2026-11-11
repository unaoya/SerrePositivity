module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 対象単射で忠実な元の関手の全射列での単射性

概要：対象と全射を区別する元の関手は後合成で全図式を区別する。
方針：対象の等式と写像の異種等式を元の関手の忠実性で反映する。
規約：元の nerve の同じ全単体を使う。
使われ方：有限部分木の射影による全 grid の整合の検査。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v' w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FaithfulObjectEmbedding
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) [F.Faithful] (hobj : Function.Injective F.obj)

include hobj in
lemma map_heq_reflect {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hX : F.obj X = F.obj X') (hY : F.obj Y = F.obj Y')
    (hf : HEq (F.map f) (F.map g)) : HEq f g := by
  have hx : X = X' := hobj hX
  have hy : Y = Y' := hobj hY
  subst X'
  subst Y'
  exact heq_of_eq (F.map_injective (eq_of_heq hf))

include hobj in
lemma postcompose_injective {I : Type w} [Category.{w'} I] :
    Function.Injective (fun G : I ⥤ C => G ⋙ F) := by
  intro G H h
  apply CategoryTheory.Functor.hext (fun i => hobj (CategoryTheory.Functor.congr_obj h i))
  intro i j f
  exact map_heq_reflect F hobj (G.map f) (H.map f)
    (CategoryTheory.Functor.congr_obj h i) (CategoryTheory.Functor.congr_obj h j)
    (CategoryTheory.Functor.hcongr_hom h f)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FaithfulObjectEmbedding
