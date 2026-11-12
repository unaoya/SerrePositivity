module

public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Basic

/-!
# 二つのファイバーの同値の全体の置換への拡張

概要：異なるファイバーは交換し、同じファイバーでは指定した同値を使う置換を構成する。
方針：添字の交換と元のファイバーの同値を従属和に移す。
規約：指定したファイバー上では元の同値そのものを回収する。
使われ方：元の自由 groupoid の持ち上げを置換表現へ移す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

def fiberSwap {I : Type u} (F : I → Type v) {i j : I} (e : F i ≃ F j) : Equiv.Perm (Σ k, F k) := by
  classical
  by_cases h : i = j
  · subst j
    exact Equiv.sigmaCongrRight (fun k => if hk : k = i then hk ▸ e else Equiv.refl _)
  · refine Equiv.sigmaCongr (Equiv.swap i j) ?_
    intro k
    by_cases hi : k = i
    · subst k
      exact e.trans (Equiv.cast (congrArg F (Equiv.swap_apply_left i j).symm))
    · by_cases hj : k = j
      · subst k
        exact e.symm.trans (Equiv.cast (congrArg F (Equiv.swap_apply_right i j).symm))
      · exact Equiv.cast (congrArg F (Equiv.swap_apply_of_ne_of_ne hi hj).symm)

lemma fiberSwap_apply {I : Type u} (F : I → Type v) {i j : I} (e : F i ≃ F j) (x : F i) :
    fiberSwap F e ⟨i, x⟩ = ⟨j, e x⟩ := by
  classical
  by_cases h : i = j
  · subst j
    simp [fiberSwap]
  · simp [fiberSwap, h, Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]

lemma fiberSwap_symm_apply {I : Type u} (F : I → Type v) {i j : I} (e : F i ≃ F j) (y : F j) :
    (fiberSwap F e).symm ⟨j, y⟩ = ⟨i, e.symm y⟩ := by
  apply (fiberSwap F e).injective
  rw [Equiv.apply_symm_apply, fiberSwap_apply, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
