module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# 元の forward 射列の終点からの同時 pullback

概要：終点への射から元の forward ブロックの全頂点を pullback し、射列を復元する。
方針：各頂点から元の終点への合成を使い、元の全隣接射で pullback の射を定める。
規約：長さ零も含む。終点だけでなく元の全頂点・全射への射影を保持する。
使われ方：分数計算で自明 fibration を左の forward ブロックへ伝える。

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

def terminalLeg (F : ComposableArrows C n) (i : Fin (n + 1)) : F.obj i ⟶ F.obj (Fin.last n) :=
  F.map (homOfLE (Fin.le_last i))

lemma terminalLeg_naturality (F : ComposableArrows C n) {i j : Fin (n + 1)} (f : i ⟶ j) :
    F.map f ≫ terminalLeg F j = terminalLeg F i := by
  rw [terminalLeg, ← CategoryTheory.Functor.map_comp]
  congr 1

lemma terminalLeg_last (F : ComposableArrows C n) :
    terminalLeg F (Fin.last n) = 𝟙 (F.obj (Fin.last n)) := F.map_id _

abbrev TerminalReplacement (C : Type u) [Category.{v} C] (n : ℕ) :=
  Comma (𝟭 C) ((evaluation (Fin (n + 1)) C).obj (Fin.last n))

variable [HasPullbacks C] (s : TerminalReplacement C n)

abbrev pullbackObj (i : Fin (n + 1)) : C := pullback (terminalLeg s.right i) s.hom

def pullbackArrow {i j : Fin (n + 1)} (f : i ⟶ j) : pullbackObj s i ⟶ pullbackObj s j :=
  pullback.map (terminalLeg s.right i) s.hom (terminalLeg s.right j) s.hom
    (s.right.map f) (𝟙 s.left) (𝟙 _) (by
      rw [Category.comp_id, terminalLeg_naturality]) (by simp)

lemma pullbackArrow_fst {i j : Fin (n + 1)} (f : i ⟶ j) :
    pullbackArrow s f ≫ pullback.fst (terminalLeg s.right j) s.hom =
      pullback.fst (terminalLeg s.right i) s.hom ≫ s.right.map f := pullback.lift_fst _ _ _

lemma pullbackArrow_snd {i j : Fin (n + 1)} (f : i ⟶ j) :
    pullbackArrow s f ≫ pullback.snd (terminalLeg s.right j) s.hom =
      pullback.snd (terminalLeg s.right i) s.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

def pullbackPath : ComposableArrows C n where
  obj := pullbackObj s
  map := pullbackArrow s
  map_id i := by
    apply pullback.hom_ext
    · rw [pullbackArrow_fst, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    · rw [pullbackArrow_snd, Category.id_comp]
  map_comp f g := by
    apply pullback.hom_ext
    · rw [pullbackArrow_fst, Category.assoc, pullbackArrow_fst,
        ← Category.assoc, pullbackArrow_fst, CategoryTheory.Functor.map_comp, Category.assoc]
    · rw [pullbackArrow_snd, Category.assoc, pullbackArrow_snd, pullbackArrow_snd]

def pullbackProjection : pullbackPath s ⟶ s.right where
  app i := pullback.fst (terminalLeg s.right i) s.hom
  naturality _ _ f := pullbackArrow_fst s f

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
