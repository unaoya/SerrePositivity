module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeFiniteHull
public import SerrePositivity.EInfinity.Hammock.QuiverTreeFiniteLeaf

/-!
# 最大高さの葉を除いた有限部分木

概要：根以外の最大高さの頂点を除いても根に関する閉性は保たれる。
方針：同じ高さの祖先は元の終点だけであることを使う。
規約：元の集合から一頂点だけを除き、親は残る。
使われ方：元の有限部分木の頂点数による帰納。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory

attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T]

def IsMaximumIn (S : Finset Q) (z : Q) : Prop :=
  ∀ x ∈ S, height T (show T from x) ≤ height T (show T from z)

lemma exists_nonroot_maximum (S : Finset Q)
    (hS : ∃ x ∈ S, (show T from x) ≠ Quiver.root T) :
    ∃ z ∈ S, (show T from z) ≠ Quiver.root T ∧ IsMaximumIn T S z := by
  obtain ⟨x, hx, hxr⟩ := hS
  obtain ⟨z, hz, hm⟩ := S.exists_max_image (fun x => height T (show T from x)) ⟨x, hx⟩
  refine ⟨z, hz, ?_, hm⟩
  intro hzr
  have hz0 : height T (show T from z) = 0 := (height_eq_zero_iff T _).mpr hzr
  have hx0 : height T (show T from x) = 0 := Nat.eq_zero_of_le_zero (hz0 ▸ hm x hx)
  exact hxr ((height_eq_zero_iff T _).mp hx0)

lemma RootClosed.erase_max {S : Finset Q} {z : Q} (hS : RootClosed T S)
    (hzr : (show T from z) ≠ Quiver.root T) (hm : IsMaximumIn T S z) :
    RootClosed T (S.erase z) := by
  refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hzr, hS.1⟩, ?_⟩
  intro x hx y hy
  obtain ⟨hxz, hxS⟩ := Finset.mem_erase.mp hx
  refine Finset.mem_erase.mpr ⟨?_, hS.2 x hxS hy⟩
  intro hyz
  subst y
  have he : height T (show T from z) = height T (show T from x) :=
    le_antisymm (rootVertices_height T hy) (hm x hxS)
  exact hxz (rootVertices_eq_of_height_mem T hy he).symm

lemma parent_mem_of_closed {S : Finset Q} {z : Q} (hS : RootClosed T S) (hz : z ∈ S)
    {p : T} (e : p ⟶ (show T from z)) : (show Q from p) ∈ S.erase z := by
  have hp : (show Q from p) ∈ rootVertices T z := by
    rw [rootVertices_arrow T e]
    exact Finset.mem_insert_of_mem (rootVertices_target T _)
  have hne : (show Q from p) ≠ z := by
    intro he
    have hh := congrArg (fun x : Q => height T (show T from x)) he
    change height T p = height T (show T from z) at hh
    have hs := height_arrow T e
    omega
  exact Finset.mem_erase.mpr ⟨hne, hS.2 z hz hp⟩

end SerrePositivity.EInfinity.Hammock.QuiverTree
