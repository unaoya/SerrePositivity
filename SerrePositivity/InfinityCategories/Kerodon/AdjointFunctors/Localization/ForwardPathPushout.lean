module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPathPullback

/-!
# 元の forward 射列の始点からの同時 pushout

概要：始点からの射で元の forward ブロックの全頂点を pushout し、射列を復元する。
方針：元の始点から各頂点への合成を使い、元の全隣接射で pushout の射を定める。
規約：長さ零も含む。元の全頂点からの射を保持する。
使われ方：分数計算で自明 cofibration を右の forward ブロックへ伝える。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {n : ℕ}

def initialLeg (F : ComposableArrows C n) (i : Fin (n + 1)) : F.obj 0 ⟶ F.obj i :=
  F.map (homOfLE (Fin.zero_le i))

lemma initialLeg_naturality (F : ComposableArrows C n) {i j : Fin (n + 1)} (f : i ⟶ j) :
    initialLeg F i ≫ F.map f = initialLeg F j := by
  rw [initialLeg, ← CategoryTheory.Functor.map_comp]
  congr 1

lemma initialLeg_zero (F : ComposableArrows C n) : initialLeg F 0 = 𝟙 (F.obj 0) := F.map_id _

abbrev InitialReplacement (C : Type u) [Category.{v} C] (n : ℕ) :=
  Comma ((evaluation (Fin (n + 1)) C).obj 0) (𝟭 C)

variable [HasPushouts C] (s : InitialReplacement C n)

abbrev pushoutObj (i : Fin (n + 1)) : C := pushout s.hom (initialLeg s.left i)

def pushoutArrow {i j : Fin (n + 1)} (f : i ⟶ j) : pushoutObj s i ⟶ pushoutObj s j :=
  pushout.map s.hom (initialLeg s.left i) s.hom (initialLeg s.left j)
    (𝟙 s.right) (s.left.map f) (𝟙 _) (by simp) (by
      rw [Category.id_comp, initialLeg_naturality])

lemma pushoutArrow_inl {i j : Fin (n + 1)} (f : i ⟶ j) :
    pushout.inl s.hom (initialLeg s.left i) ≫ pushoutArrow s f =
      pushout.inl s.hom (initialLeg s.left j) :=
  (pushout.inl_desc _ _ _).trans (Category.id_comp _)

lemma pushoutArrow_inr {i j : Fin (n + 1)} (f : i ⟶ j) :
    pushout.inr s.hom (initialLeg s.left i) ≫ pushoutArrow s f =
      s.left.map f ≫ pushout.inr s.hom (initialLeg s.left j) := pushout.inr_desc _ _ _

def pushoutPath : ComposableArrows C n where
  obj := pushoutObj s
  map := pushoutArrow s
  map_id i := by
    apply pushout.hom_ext
    · rw [pushoutArrow_inl, Category.comp_id]
    · rw [pushoutArrow_inr, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply pushout.hom_ext
    · rw [pushoutArrow_inl, ← Category.assoc, pushoutArrow_inl, pushoutArrow_inl]
    · rw [pushoutArrow_inr, ← Category.assoc, pushoutArrow_inr,
        Category.assoc, pushoutArrow_inr, CategoryTheory.Functor.map_comp, Category.assoc]

def pushoutInclusion : s.left ⟶ pushoutPath s where
  app i := pushout.inr s.hom (initialLeg s.left i)
  naturality _ _ f := (pushoutArrow_inr s f).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
