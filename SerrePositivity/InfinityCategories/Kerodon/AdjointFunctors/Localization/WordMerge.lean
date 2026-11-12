module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word
public import Mathlib.Order.Fin.Basic

/-!
# 同方向の隣接二列を合成する元の語の写像

概要：同じ向きの隣接二列だけを同一視する全射な語の写像を構成する。
方針：Fin.predAbove の順序写像と同じ方向の等式を使う。
規約：一つの fiber だけが二列であり、元の色と順序を保持する。
使われ方：未縮約 hammock の基本合成縮約。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

/-- 右側の列を一つ省いた元の列の方向列。 -/
def mergeTarget {n : ℕ} (d : Fin (n + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word :=
  ⟨n + 1, fun i => d (p.succ.succAbove i)⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (mergeTarget)


/-- 元の同方向の隣接二列だけを合成する全射。 -/
def mergeMap {n : ℕ} (d : Fin (n + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p : Fin (n + 1))
    (hp : d p.castSucc = d p.succ) : (⟨n + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) ⟶ mergeTarget d p where
  orderHom := p.predAboveOrderHom
  direction_eq j := by
    by_cases hj : j = p.succ
    · subst j
      change d (p.succ.succAbove (p.predAbove p.succ)) = d p.succ
      rw [Fin.predAbove_succ_self, Fin.succAbove_succ_self]
      exact hp
    · exact congrArg d (Fin.succ_succAbove_predAbove hj)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (mergeMap)


lemma mergeMap_surjective {n : ℕ} (d : Fin (n + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p : Fin (n + 1))
    (hp : d p.castSucc = d p.succ) : Function.Surjective (mergeMap d p hp).orderHom :=
  Fin.predAbove_surjective p

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (mergeMap_surjective)


lemma mergeMap_left {n : ℕ} (d : Fin (n + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p : Fin (n + 1))
    (hp : d p.castSucc = d p.succ) : (mergeMap d p hp).orderHom p.castSucc = p :=
  Fin.predAbove_castSucc_self p

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (mergeMap_left)


lemma mergeMap_right {n : ℕ} (d : Fin (n + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p : Fin (n + 1))
    (hp : d p.castSucc = d p.succ) : (mergeMap d p hp).orderHom p.succ = p :=
  Fin.predAbove_succ_self p

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (mergeMap_right)


/-- 合成される唯一の二列の fiber は、元の隣接二列そのもの。 -/
lemma mergeMap_fiber {n : ℕ} (d : Fin (n + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p : Fin (n + 1))
    (hp : d p.castSucc = d p.succ) (j : Fin (n + 2)) :
    (mergeMap d p hp).orderHom j = p ↔ j = p.castSucc ∨ j = p.succ := by
  change p.predAbove j = p ↔ _
  constructor
  · intro h
    by_cases hj : j = p.succ
    · exact Or.inr hj
    · have he := Fin.succ_succAbove_predAbove hj
      rw [h, Fin.succAbove_succ_self] at he
      exact Or.inl he.symm
  · rintro (rfl | rfl)
    · exact Fin.predAbove_castSucc_self p
    · exact Fin.predAbove_succ_self p

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (mergeMap_fiber)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
