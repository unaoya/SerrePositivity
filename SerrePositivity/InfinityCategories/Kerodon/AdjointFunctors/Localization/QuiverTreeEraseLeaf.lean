module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteHull
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteLeaf

/-!
# 最大高さの葉を除いた有限部分木

概要：根以外の最大高さの頂点を除いても根に関する閉性は保たれる。
方針：同じ高さの祖先は元の終点だけであることを使う。
規約：元の集合から一頂点だけを除き、親は残る。
使われ方：元の有限部分木の頂点数による帰納。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T]

def IsMaximumIn (S : Finset Q) (z : Q) : Prop :=
  ∀ x ∈ S, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from x) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from z)

lemma exists_nonroot_maximum (S : Finset Q)
    (hS : ∃ x ∈ S, (show T from x) ≠ Quiver.root T) :
    ∃ z ∈ S, (show T from z) ≠ Quiver.root T ∧ IsMaximumIn T S z := by
  obtain ⟨x, hx, hxr⟩ := hS
  obtain ⟨z, hz, hm⟩ := S.exists_max_image (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from x)) ⟨x, hx⟩
  refine ⟨z, hz, ?_, hm⟩
  intro hzr
  have hz0 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from z) = 0 := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height_eq_zero_iff T _).mpr hzr
  have hx0 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from x) = 0 := Nat.eq_zero_of_le_zero (hz0 ▸ hm x hx)
  exact hxr ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height_eq_zero_iff T _).mp hx0)

lemma RootClosed.erase_max {S : Finset Q} {z : Q} (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T S)
    (hzr : (show T from z) ≠ Quiver.root T) (hm : IsMaximumIn T S z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T (S.erase z) := by
  refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hzr, hS.1⟩, ?_⟩
  intro x hx y hy
  obtain ⟨hxz, hxS⟩ := Finset.mem_erase.mp hx
  refine Finset.mem_erase.mpr ⟨?_, hS.2 x hxS hy⟩
  intro hyz
  subst y
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from z) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from x) :=
    le_antisymm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices_height T hy) (hm x hxS)
  exact hxz (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices_eq_of_height_mem T hy he).symm

lemma parent_mem_of_closed {S : Finset Q} {z : Q} (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T S) (hz : z ∈ S)
    {p : T} (e : p ⟶ (show T from z)) : (show Q from p) ∈ S.erase z := by
  have hp : (show Q from p) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices T z := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices_arrow T e]
    exact Finset.mem_insert_of_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices_target T _)
  have hne : (show Q from p) ≠ z := by
    intro he
    have hh := congrArg (fun x : Q => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from x)) he
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T p = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height T (show T from z) at hh
    have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.height_arrow T e
    omega
  exact Finset.mem_erase.mpr ⟨hne, hS.2 z hz hp⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
