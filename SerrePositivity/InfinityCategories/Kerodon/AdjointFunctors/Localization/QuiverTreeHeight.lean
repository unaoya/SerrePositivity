module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeExhaustion

/-!
# 木の根からの高さと生成辺

概要：木の辺は高さを一つ増やし、全生成辺の両端の高さは一つ違う。
方針：根からの射列の一意性を連結した射列へ適用する。
規約：元の部分 quiver の根と実際の射列の長さを使う。
使われ方：有限部分木の最大高さの葉を選ぶ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T]

def rootPath (x : T) : Quiver.Path (Quiver.root T) x :=
  (Quiver.Arborescence.uniquePath x).default

def height (x : T) : ℕ := (rootPath T x).length

lemma height_root : height T (Quiver.root T) = 0 := by
  have h : rootPath T (Quiver.root T) = Quiver.Path.nil :=
    Subsingleton.elim _ _
  exact congrArg Quiver.Path.length h

lemma height_arrow {x y : T} (e : x ⟶ y) : height T y = height T x + 1 := by
  have h : rootPath T y = (rootPath T x).cons e := Subsingleton.elim _ _
  exact congrArg Quiver.Path.length h

lemma height_eq_zero_iff (x : T) : height T x = 0 ↔ x = Quiver.root T := by
  constructor
  · intro h
    exact (Quiver.Path.eq_of_length_zero (rootPath T x) h).symm
  · rintro rfl
    exact height_root T

lemma parent_exists (x : T) (hx : x ≠ Quiver.root T) :
    ∃ (y : T) (_ : y ⟶ x), height T x = height T y + 1 := by
  cases hp : rootPath T x with
  | nil => exact False.elim (hx rfl)
  | cons p e => exact ⟨_, e, height_arrow T e⟩

lemma incoming_unique {x y z : T} (e : x ⟶ z) (f : y ⟶ z) : x = y ∧ HEq e f := by
  have h : (default : Quiver.Path (Quiver.root T) x).cons e =
      (default : Quiver.Path (Quiver.root T) y).cons f := Subsingleton.elim _ _
  cases h
  exact ⟨rfl, HEq.rfl⟩

lemma positive_height {x y : Q} (f : x ⟶ y) (hf : f.toPos ∈ T x y) :
    height T (show T from y) = height T (show T from x) + 1 :=
  height_arrow T (⟨f.toPos, hf⟩ : (show T from x) ⟶ (show T from y))

lemma negative_height {x y : Q} (f : x ⟶ y) (hf : f.toNeg ∈ T y x) :
    height T (show T from x) = height T (show T from y) + 1 :=
  height_arrow T (⟨f.toNeg, hf⟩ : (show T from y) ⟶ (show T from x))

variable [Quiver.IsThin (Quiver.FreeGroupoid Q)]

lemma edge_height {x y : Q} (f : x ⟶ y) :
    height T (show T from y) = height T (show T from x) + 1 ∨
      height T (show T from x) = height T (show T from y) + 1 := by
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.every_edge_in_tree T f with hf | hf
  · exact Or.inl (positive_height T f hf)
  · exact Or.inr (negative_height T f hf)

include T in
lemma no_loop {x : Q} (f : x ⟶ x) : False := by
  rcases edge_height T f with h | h <;> omega

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
