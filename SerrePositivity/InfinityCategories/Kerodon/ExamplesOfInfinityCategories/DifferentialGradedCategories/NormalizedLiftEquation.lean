module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedLift

/-!
# 正規化への持ち上げの標準方程式

概要：二成分の持ち上げは標準の単体の方程式を満たす。
方針：削除和の支持を調べ、最上位では δz、他では零と計算する。
規約：微分の二乗が零であることを零番目の面に使う。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化の評価の逆構成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：二成分の持ち上げの最上位以外の削除和は零である。
方針：削除した集合が支持点になれば元の集合は全体集合となることを使う。
規約：空でない集合とその許される次数で評価する。
使われ方：HA 1.3.1.12 の標準方程式の支持外計算。 -/
lemma standardRhs_lift_other {n : ℕ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-(n + 1 : ℤ)))
    (J : Finset (Fin (n + 2))) (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (hfull : J ≠ Finset.univ) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData z) J k hk = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs
  split_ifs with hJ
  · apply Finset.sum_eq_zero
    intro j _
    have h₁ : J.erase j.val ≠ Finset.univ := by
      intro he
      have : j.val ∈ J.erase j.val := by rw [he]; simp
      simp at this
    have h₂ : J.erase j.val ≠ Finset.univ.erase 0 := by
      intro he
      have hj : j.val = 0 := by
        by_contra hj
        have : j.val ∈ J.erase j.val := by rw [he]; simp [hj]
        simp at this
      apply hfull
      apply Finset.eq_univ_of_forall
      intro a
      by_cases ha : a = j.val
      · exact ha ▸ j.property
      · have : a ∈ J.erase j.val := by rw [he]; simp [← hj, ha]
        exact (Finset.mem_erase.mp this).2
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_other z _ _ _ _ h₁ h₂, smul_zero]
  · rfl

/-- 概要：二成分の持ち上げの最上位の削除和は δz である。
方針：零番目の削除項を取り出し、他の削除項の支持を除外する。
規約：昇順の境界符号の零番目は +1。
使われ方：HA 1.3.1.12 の最上位の標準方程式。 -/
lemma standardRhs_lift_top {n : ℕ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-(n + 1 : ℤ))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData z) Finset.univ (-(n + 1 : ℤ)) (by simp) =
      differential R z := by
  have hu : 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card := by simp
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs, dite_eq_left hu]
  rw [Finset.sum_eq_single (⟨0, Finset.mem_univ _⟩ :
    (Finset.univ : Finset (Fin (n + 2))))]
  · have hf : (Finset.univ : Finset (Fin (n + 2))).filter (· < 0) = ∅ := by ext; simp
    rw [hf, Finset.card_empty, pow_zero, one_smul, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_face]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := fun he ↦ hj (Subtype.ext he)
    have h₁ : (Finset.univ.erase j.val : Finset (Fin (n + 2))) ≠ Finset.univ := by
      intro he
      have : j.val ∈ Finset.univ.erase j.val := by rw [he]; simp
      simp at this
    have h₂ : (Finset.univ.erase j.val : Finset (Fin (n + 2))) ≠
        Finset.univ.erase 0 := by
      intro he
      have : (0 : Fin (n + 2)) ∈ Finset.univ.erase j.val := by simp [Ne.symm hj0]
      rw [he] at this
      simp at this
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_other z _ _ _ _ h₁ h₂, smul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- 概要：二成分の持ち上げは標準単体の方程式を満たす。
方針：最上位、零番目の面、その他に分け、δ²=0 と支持の消滅を使う。
規約：追加の閉性の仮定は不要で、任意の負次数の元を使う。
使われ方：HA 1.3.1.12 の正規化の全射性の候補。 -/
lemma normalizedLiftData_mem_standard {n : ℕ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-(n + 1 : ℤ))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData z ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSubmodule R x y (n + 1) := by
  intro J k hJ hk
  by_cases hfull : J = Finset.univ
  · subst J
    have hkk : k = -(n + 1 : ℤ) := by simp at hk; omega
    subst hkk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_top, standardRhs_lift_top]
  rw [standardRhs_lift_other z J k hk hfull]
  by_cases hface : J = Finset.univ.erase 0
  · subst J
    have hkk : k = -(n + 1 : ℤ) + 1 := by simp at hk; omega
    subst hkk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_face]
    exact congrArg (fun d ↦ d z)
      ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d_comp_d (-(n + 1 : ℤ)) (-(n + 1 : ℤ) + 1)
        (-(n + 1 : ℤ) + 1 + 1))
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_other z J k hJ hk hfull hface]
    exact map_zero _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
