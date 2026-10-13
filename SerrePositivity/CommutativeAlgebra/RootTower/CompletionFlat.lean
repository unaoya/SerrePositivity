module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # 根の塔と完備化上の正則元

未完備の根の塔の平坦性を基底環へ制限し、主イデアルの完備化でその生成元の
正則性が保存されることを示す。後者は逆極限の一段先の座標で直接証明する。
完備化した塔の基底環上の平坦性や、任意の有限代数とのテンソル積の平坦性は
このモジュールでは主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity

/-- 正則元が生成する主イデアルについて、完備化上でもその元は正則。
第 `n+1` 座標で生成元をキャンセルし、第 `n` 座標が零であることを示す。 -/
theorem isSMulRegular_adicCompletion_span_singleton
    (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a) :
    IsSMulRegular (AdicCompletion (Ideal.span {a}) R)
      (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  obtain ⟨v, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {a}) R x
  apply AdicCompletion.ext_evalₐ
  intro n
  have hx' : a * v.val (n + 1) ∈ (Ideal.span {a}) ^ (n + 1) := by
    have he := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (n + 1)) hx
    change Ideal.Quotient.mk ((Ideal.span {a}) ^ (n + 1)) (a * v.val (n + 1)) = 0 at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx'
  obtain ⟨z, hz⟩ := hx'
  have hv : v.val (n + 1) = a ^ n * z := by
    apply ha
    change a * v.val (n + 1) = a * (a ^ n * z)
    simpa [pow_succ', mul_assoc] using hz
  have hvmem : v.val (n + 1) ∈ (Ideal.span {a}) ^ n := by
    rw [hv, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  have hdelta := v.property (Nat.le_succ n)
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hdelta
  have hn : v.val n ∈ (Ideal.span {a}) ^ n := by
    simpa using (Ideal.span {a} ^ n).add_mem hdelta hvmem
  simpa only [AdicCompletion.evalₐ_mk, map_zero] using
    Ideal.Quotient.eq_zero_iff_mem.mpr hn

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 未完備の根の塔は基底環上平坦。零段の有限自由性と塔の各段上の平坦性を合成する。 -/
theorem flat_tower_over_base : Module.Flat A (Tower A t p) := by
  let := towerStage_free A t p 0
  let := flat_tower A t p 0
  exact Module.Flat.trans A (TowerStage A t p 0) (Tower A t p)

/-- 基底環上で `p` が正則なら、完備化した根の塔上でも `p` は正則。
未完備の塔の平坦性と、主イデアル完備化上の正則性保存を用いる。 -/
theorem isSMulRegular_p_completedTower (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (CompletedTower A t p) (p : CompletedTower A t p) := by
  let := flat_tower_over_base A t p
  have ht : IsSMulRegular (Tower A t p) (p : Tower A t p) := by
    simpa using hp.of_flat (S := Tower A t p)
  simpa using isSMulRegular_adicCompletion_span_singleton (Tower A t p) (p : Tower A t p) ht

end Section2
end SerrePositivity
