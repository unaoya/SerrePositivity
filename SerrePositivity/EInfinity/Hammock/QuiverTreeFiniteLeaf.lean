module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeLeaf
public import Mathlib.Data.Finset.Max

/-!
# 有限頂点集合における最大高さの葉

概要：有限非空頂点集合には、その集合内の入る対称生成辺が一意な頂点がある。
方針：高さの最大値を選び、全ての隣接頂点から入る辺に木の一意性を適用する。
規約：集合内の辺そのものを比較し、元の quiver の向きを保持する。
使われ方：有限部分木の葉を一つずつ除く。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q]

def IsLeafIn (S : Finset Q) (z : Q) : Prop :=
  ∀ {x y : Quiver.Symmetrify Q}, x ∈ S → y ∈ S →
    ∀ (e : x ⟶ z) (f : y ⟶ z), x = y ∧ HEq e f

variable (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] [Quiver.IsThin (Quiver.FreeGroupoid Q)]

lemma leaf_of_max_height (S : Finset Q) (z : Q)
    (h : ∀ x ∈ S, height T (show T from x) ≤ height T (show T from z)) : IsLeafIn S z := by
  intro x y hx hy e f
  exact higher_incoming_unique T e f (h x hx) (h y hy)

include T in
lemma exists_finite_leaf (S : Finset Q) (hS : S.Nonempty) :
    ∃ z ∈ S, IsLeafIn S z := by
  obtain ⟨z, hz, hmax⟩ := S.exists_max_image (fun x => height T (show T from x)) hS
  exact ⟨z, hz, leaf_of_max_height T S z hmax⟩

lemma exists_nonroot_finite_leaf (S : Finset Q)
    (hS : ∃ x ∈ S, (show T from x) ≠ Quiver.root T) :
    ∃ z ∈ S, (show T from z) ≠ Quiver.root T ∧ IsLeafIn S z := by
  obtain ⟨x, hx, hxr⟩ := hS
  obtain ⟨z, hz, hmax⟩ := S.exists_max_image (fun x => height T (show T from x)) ⟨x, hx⟩
  refine ⟨z, hz, ?_, leaf_of_max_height T S z hmax⟩
  intro hzr
  have hzero : height T (show T from z) = 0 := (height_eq_zero_iff T _).mpr hzr
  have hxzero : height T (show T from x) = 0 := Nat.eq_zero_of_le_zero (hzero ▸ hmax x hx)
  exact hxr ((height_eq_zero_iff T _).mp hxzero)

end SerrePositivity.EInfinity.Hammock.QuiverTree
