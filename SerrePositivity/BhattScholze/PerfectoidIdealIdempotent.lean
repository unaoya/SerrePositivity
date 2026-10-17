module

public import SerrePositivity.BhattScholze.PerfectoidIdealLemma103
public import SerrePositivity.CLMST.Almost

/-!
# Remark 10.7 の mod p 冪の冪等性
## 概要
perfectoid 化の核 K の mod pⁿ 像は冪等である（BS 著者版 Remark 10.7、印刷 p.80）。
## 方針
Lemma 10.3 の実自己積から既存の Tor₁・conormal 比較を通じて K/K² の p 可除性を得る。
それを反復し K=K²+pⁿK を証明して、既存の像イデアルの冪等性判定を使う。
## 規約
CLMST.Almost の既存の像イデアルの略記だけを利用し、入力引用は使わない。
## 使われ方
CLMST の BasicSetup と同じ署名で冪等性を渡す。BasicSetup 自体は編集しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/--
## 概要
perfectoid 化の核 K の conormal 加群 K/K² は全 pⁿ で可除である。
## 方針
Lemma 10.3 の商自己積から実 Tor₁ の p 可除性を得て既存の conormal 比較で移し、反復する。
## 規約
通常の conormal 加群を使い、p ねじれの有無を仮定しない。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の冪等性の計算に使う。
-/
theorem perfectoidIdeal_conormal_pow_smul_surjective (n : ℕ) :
    Function.Surjective
      (fun x : (perfectoidIdeal R p hR g).Cotangent => (p : R) ^ n • x) := by
  have h := (quotientTorOne_smul_surjective_iff_conormal R
    (perfectoidIdeal R p hR g) (p : R)).mp
    (quotientTorOne_smul_surjective_of_completed_mul_isIso (p : R)
      (perfectoidIdeal R p hR g) (perfectoidIdeal_lemma103 R p hR g).2.1)
  induction n with
  | zero =>
    intro x
    exact ⟨x, by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨y, hy⟩ := ih x
    obtain ⟨z, hz⟩ := h y
    refine ⟨z, ?_⟩
    change (p : R) ^ n • y = x at hy
    change (p : R) • z = y at hz
    change (p : R) ^ (n + 1) • z = x
    rw [pow_succ, mul_smul, hz, hy]

/--
## 概要
perfectoid 化の核 K は K²+pⁿK に等しい。n=1 は K=K²+pK を与える。
## 方針
conormal 加群の pⁿ 可除性の原像を K に持ち上げ、差が K² に属することを使う。
## 規約
pⁿK は span{pⁿ} と K のイデアル積で明示する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の mod pⁿ 冪等性の中間等式である。
-/
theorem perfectoidIdeal_eq_square_sup_pow_mul (n : ℕ) :
    let K := perfectoidIdeal R p hR g
    K = K * K ⊔ Ideal.span {(p : R) ^ n} * K := by
  let K := perfectoidIdeal R p hR g
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := perfectoidIdeal_conormal_pow_smul_surjective R p hR g n
      (K.toCotangent ⟨x, hx⟩)
    obtain ⟨z, rfl⟩ := K.toCotangent_surjective y
    change (p : R) ^ n • K.toCotangent z = K.toCotangent ⟨x, hx⟩ at hy
    have hz : K.toCotangent (⟨x, hx⟩ - (p : R) ^ n • z) = 0 := by
      rw [map_sub, map_smul, hy, sub_self]
    have hmem : x - (p : R) ^ n * (z : R) ∈ K * K := by
      have hz₂ := (K.toCotangent_eq_zero _).mp hz
      change x - (p : R) ^ n * (z : R) ∈ K ^ 2 at hz₂
      simpa only [pow_two] using hz₂
    have hpz : (p : R) ^ n * (z : R) ∈ Ideal.span {(p : R) ^ n} * K :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) z.property
    exact Submodule.mem_sup.mpr ⟨_, hmem, _, hpz, sub_add_cancel _ _⟩
  · exact sup_le Ideal.mul_le_left Ideal.mul_le_right

/--
## 概要
単項商の perfectoid 化の核の mod pᴺ 像は冪等である
（BS 著者版 Remark 10.7、印刷 p.80）。
## 方針
実商自己積の同型性から、既存の Tor₁・conormal・像イデアルの冪等性判定を適用する。
## 規約
CLMST.Inputs.perfectoidIdealMod_idempotent と同じ署名を保持し、N=0 も含む。
## 使われ方
既存の入力引用を使わずに CLMST へ渡す証明済み入口である。
-/
theorem perfectoidIdealMod_idempotent (N : ℕ) :
    CLMST.perfectoidIdealMod R p hR g N * CLMST.perfectoidIdealMod R p hR g N =
      CLMST.perfectoidIdealMod R p hR g N :=
  ideal_mod_power_idempotent_of_completed_quotient_mul_isIso (p : R)
    (perfectoidIdeal R p hR g) (perfectoidIdeal_lemma103 R p hR g).2.1 N

end SerrePositivity.BhattScholze
