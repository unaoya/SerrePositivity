module

public import Mathlib.RingTheory.Perfection
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Tactic.Ring
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Nilpotent.Basic
public import SerrePositivity.CommutativeAlgebra.Perfection
public import SerrePositivity.CommutativeAlgebra.PerfectRing
public import SerrePositivity.CommutativeAlgebra.Adic.Principal
public import Mathlib.RingTheory.Perfectoid.Untilt
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Regular.Basic

/-! # Fontaine 核と perfectoid 性の判定

## 概要

Fontaine の写像 θ の核の生成元を同定し、それによって整 perfectoid 性を判定する。第一 Witt 係数が単元の元（primitive な形）が核を生成すること（BMS Lemma 3.10(i)）、標数 p では核が p で生成され整 perfectoid 環が完全で被約なこと（BMS Example 3.15）、核の特別な生成元から最初の Frobenius 核を計算すること、第 0 係数の生成から核の生成元を持ち上げること、核進・主イデアル進の分離性（BS の F7 の仮定 `IsHausdorff (ker θ)` を供給する）、両立する p 冪根から tilt の元を作り最初の Frobenius 核だけから perfectoid 性を導くこと（`isIntegralPerfectoid_of_compatible_p_roots`）を与える。

## 方針

Witt ベクトルの単元判定、perfect 環の主イデアル商の Frobenius、Perfection の係数による冪等元・単元の検出を部品として分け、核の生成元の同定と商への移送を別の段にする。Witt 環の p 進完備性で第 0 係数の生成を核全体へ持ち上げる。

## 規約

出典は BMS『Integral p-adic Hodge theory』（https://arxiv.org/pdf/1602.03148、印刷 pp.22–23）。`isIntegralPerfectoid_of_compatible_p_roots` は RootTower/Perfectoid が使う。完全環の被約性は `PerfectRing` の `isReduced_of_perfectPower` を使う。

## 使われ方

BhattScholze の perfect prism と perfectoid 環の比較、CLMST の完備塔、`RootTower/Perfectoid`、`Perfectoid/Torsion`。
-/

@[expose] public noncomputable section

universe u

section PerfectionIdempotentsPart

namespace SerrePositivity

/-- Perfection の冪等元は、第零係数が零なら零。 -/
theorem perfection_idempotent_eq_zero_of_coeff_zero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (e : Perfection R p) (he : IsIdempotentElem e)
    (hzero : Perfection.coeff R p 0 e = 0) : e = 0 := by
  apply Perfection.ext
  intro n
  have hn : IsIdempotentElem (Perfection.coeff R p n e) := by
    change Perfection.coeff R p n e * Perfection.coeff R p n e = Perfection.coeff R p n e
    rw [← map_mul, he.eq]
  have hp := Perfection.coeffMonoidHom_pow_p_pow_self e n
  change (Perfection.coeff R p n e) ^ (p ^ n) = Perfection.coeff R p 0 e at hp
  rw [hn.pow_eq (pow_ne_zero n (Fact.out : p.Prime).ne_zero), hzero] at hp
  simpa only [map_zero] using hp

/-- Perfection の第零係数が単元なら、各係数の逆元から元全体の逆元を構成できる。 -/
theorem perfection_isUnit_of_coeff_zero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (a : Perfection R p) (ha : IsUnit (Perfection.coeff R p 0 a)) : IsUnit a := by
  have hunit (n : ℕ) : IsUnit (Perfection.coeff R p n a) := by
    apply (isUnit_pow_iff (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp
    rw [show (Perfection.coeff R p n a) ^ (p ^ n) = Perfection.coeff R p 0 a from
      Perfection.coeffMonoidHom_pow_p_pow_self a n]
    exact ha
  let b : Perfection R p := ⟨fun n ↦ Ring.inverse (Perfection.coeff R p n a), by
    intro n
    rw [Ring.inverse_pow, show (Perfection.coeff R p (n + 1) a) ^ p =
      Perfection.coeff R p n a from Perfection.coeffMonoidHom_pow_p' a n]⟩
  apply IsUnit.of_mul_eq_one b
  apply Perfection.ext
  intro n
  change Perfection.coeff R p n a * Ring.inverse (Perfection.coeff R p n a) = 1
  exact Ring.mul_inverse_cancel _ (hunit n)

/-- 第零・第一係数の積方程式と冪等元の検出から、因子の単元性を得る。
Wittベクトル自体の計算とは独立の可換環の補題。 -/
theorem isUnit_of_coefficient_equations
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hdetect : ∀ e : R, IsIdempotentElem e → f e = 0 → e = 0)
    (x a b y : R) (N : ℕ) (hN : 0 < N) (hxa : x * a = 0)
    (hfirst : x ^ N * b + y * a ^ N = 1) (hfx : f x = 0) : IsUnit a := by
  let e := x ^ N * b
  have hprod : e * (y * a ^ N) = 0 := by
    calc
      _ = (x * a) ^ N * (b * y) := by dsimp only [e]; ring
      _ = 0 := by rw [hxa, zero_pow (Nat.ne_of_gt hN), zero_mul]
  have hidem : IsIdempotentElem e := by
    have heq := congrArg (fun z : R ↦ e * z) hfirst
    change e * (e + y * a ^ N) = e * 1 at heq
    rw [mul_add, hprod, add_zero, mul_one] at heq
    exact heq
  have hfe : f e = 0 := by
    simp only [e, map_mul, map_pow, hfx, zero_pow (Nat.ne_of_gt hN), zero_mul]
  have hezero := hdetect e hidem hfe
  have hone : y * a ^ N = 1 := by
    change e + y * a ^ N = 1 at hfirst
    simpa only [hezero, zero_add] using hfirst
  exact (isUnit_pow_iff (Nat.ne_of_gt hN)).mp (IsUnit.of_mul_eq_one_right y hone)

end SerrePositivity

end PerfectionIdempotentsPart

section PerfectoidFrobeniusCriterionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.PerfectoidFrobeniusCriterion

section PerfectRing

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- Perfect 環の Frobenius は、主イデアル商 `K/(q)` と `K/(q^p)` の環同型を与える。
BMS 判定の最終段階で、tilt 上の Frobenius を実際の商の同型として使う。 -/
def perfectFrobeniusQuotientEquiv (q : K) :
    K ⧸ Ideal.span {q} ≃+* K ⧸ Ideal.span {q ^ p} :=
  Ideal.quotientEquiv (Ideal.span {q}) (Ideal.span {q ^ p}) (frobeniusEquiv K p) (by
    rw [Ideal.map_span, Set.image_singleton]
    rfl)

/-- 主イデアル商の Frobenius 同型は、代表元を p 乗する写像である。 -/
@[simp] theorem perfectFrobeniusQuotientEquiv_mk (q x : K) :
    perfectFrobeniusQuotientEquiv K p q (Ideal.Quotient.mk (Ideal.span {q}) x) =
      Ideal.Quotient.mk (Ideal.span {q ^ p}) (x ^ p) := rfl

/-- Perfect 環の Witt ベクトルは、定数係数が単元なら単元。
Witt mod p の同型と、p 進完備性による Jacobson 根基への包含を使う。 -/
theorem witt_isUnit_of_constantCoeff (x : WittVector p K) (hx : IsUnit (x.coeff 0)) :
    IsUnit x := by
  let I : Ideal (WittVector p K) := Ideal.span {(p : WittVector p K)}
  let := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
  let e := WittVector.quotientPEquiv (p := p) (k := K)
  have he : IsUnit (e (Ideal.Quotient.mk I x)) := by
    change IsUnit (x.coeff 0)
    exact hx
  have hq : IsUnit (Ideal.Quotient.mk I x) := by
    have hq' := he.map e.symm.toMonoidHom
    change IsUnit (e.symm (e (Ideal.Quotient.mk I x))) at hq'
    simpa only [RingEquiv.symm_apply_apply] using hq'
  exact isUnit_of_map_unit (Ideal.Quotient.mk I) x hq

end PerfectRing

section Fontaine

variable (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- 単項な Fontaine 核の元で、第1 Witt 係数の mod p 投影が単元なら、その元は核を生成する。
既存の生成元との積を第1係数で比較し、Perfection と Witt の単元検出を順に用いる。 -/
theorem ker_fontaineTheta_eq_span_of_firstCoeff_unit
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (ξ : WittVector p (PreTilt S p))
    (hξ : ξ ∈ RingHom.ker (WittVector.fontaineTheta S p))
    (hfirst : IsUnit (PreTilt.coeff 0 (ξ.coeff 1))) :
    RingHom.ker (WittVector.fontaineTheta S p) = Ideal.span {ξ} := by
  let K := RingHom.ker (WittVector.fontaineTheta S p)
  let : K.IsPrincipal := hker
  let η : WittVector p (PreTilt S p) := Submodule.IsPrincipal.generator K
  have hgen : Ideal.span {η} = K := Ideal.span_singleton_generator K
  have hη : η ∈ K := Submodule.IsPrincipal.generator_mem K
  have hdiv : η ∣ ξ := by
    apply Ideal.mem_span_singleton.mp
    rwa [hgen]
  obtain ⟨a, ha⟩ := hdiv
  have hηzero : PreTilt.coeff 0 (η.coeff 0) = 0 := by
    rw [← WittVector.mk_fontaineTheta]
    have hθ : WittVector.fontaineTheta S p η = 0 := hη
    rw [hθ, map_zero]
  have hcoeff : PreTilt.coeff 0 (ξ.coeff 1) =
      PreTilt.coeff 0 (η.coeff 1) * (PreTilt.coeff 0 (a.coeff 0)) ^ p := by
    rw [ha, witt_mul_coeff_one, map_add, map_add, map_mul, map_mul, map_pow,
      hηzero, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul, zero_add]
    simp only [CharP.cast_eq_zero, zero_mul, map_zero, add_zero, map_pow]
  have hapow : IsUnit ((PreTilt.coeff 0 (a.coeff 0)) ^ p) := by
    rw [hcoeff] at hfirst
    exact isUnit_of_mul_isUnit_right hfirst
  have ha0unit : IsUnit (a.coeff 0) :=
    perfection_isUnit_of_coeff_zero (ModP S p) p (a.coeff 0)
      ((isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp hapow)
  have haunit : IsUnit a := witt_isUnit_of_constantCoeff (PreTilt S p) p a ha0unit
  rw [ha, Ideal.span_singleton_mul_right_unit haunit, hgen]

/-- Untilting した元の p 乗が (p) に属すれば、その第零 tilt 成分の p 乗は零。 -/
theorem coeff_zero_pow_eq_zero_of_untilt_pow_mem_p
    (q : PreTilt S p) (hq : q.untilt ^ p ∈ Ideal.span {(p : S)}) :
    (PreTilt.coeff 0 q) ^ p = 0 := by
  rw [← PreTilt.mk_untilt_eq_coeff_zero, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hq

omit [IsAdicComplete (Ideal.span {(p : S)}) S] in
/-- `p+[q]^N x` の第1係数のmod p投影は1。
Witt の係数加算公式を展開せず、第零 tilt 成分への Witt.map がこの元を p に送ることを使う。 -/
theorem primitive_shape_firstCoeff_eq_one_of_power
    (q : PreTilt S p) (x : WittVector p (PreTilt S p))
    (N : ℕ) (hq : (PreTilt.coeff 0 q) ^ N = 0) :
    PreTilt.coeff 0
      (((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ N * x).coeff 1) = 1 := by
  have hmap : WittVector.map (PreTilt.coeff 0)
      ((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ N * x) =
        (p : WittVector p (ModP S p)) := by
    simp only [map_add, map_natCast, map_mul, map_pow, WittVector.map_teichmuller]
    rw [← map_pow, hq, WittVector.teichmuller_zero, zero_mul, add_zero]
  have hcoeff := congrArg (fun w : WittVector p (ModP S p) ↦ w.coeff 1) hmap
  simpa only [WittVector.map_coeff, WittVector.coeff_p_one] using hcoeff

omit [IsAdicComplete (Ideal.span {(p : S)}) S] in
/-- p乗の場合の互換入口。 -/
theorem primitive_shape_firstCoeff_eq_one
    (q : PreTilt S p) (x : WittVector p (PreTilt S p))
    (hq : (PreTilt.coeff 0 q) ^ p = 0) :
    PreTilt.coeff 0
      (((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * x).coeff 1) = 1 :=
  primitive_shape_firstCoeff_eq_one_of_power S p q x p hq

/-- 上記の特別な核の元は、単項な Fontaine 核を生成する。
`q.untilt^p∈(p)` から第1係数の単元性を実証明し、生成元の同定へ接続する。 -/
theorem ker_fontaineTheta_eq_span_primitive_shape
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (q : PreTilt S p) (x : WittVector p (PreTilt S p))
    (hq : q.untilt ^ p ∈ Ideal.span {(p : S)})
    (hξ : (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * x ∈
      RingHom.ker (WittVector.fontaineTheta S p)) :
    RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * x} := by
  apply ker_fontaineTheta_eq_span_of_firstCoeff_unit S p hker _ hξ
  rw [primitive_shape_firstCoeff_eq_one S p q x
    (coeff_zero_pow_eq_zero_of_untilt_pow_mem_p S p q hq)]
  exact isUnit_one

/-- 剰余 Frobenius が全射なら、任意の元には mod p で一致する untilt がある。 -/
theorem exists_untilt_eq_mod_p
    (hF : Function.Surjective (frobenius (ModP S p) p)) (a : S) :
    ∃ q : PreTilt S p,
      q.untilt - a ∈ Ideal.span {(p : S)} := by
  obtain ⟨q, hq⟩ := Perfection.coeff_surjective hF 0
    (Ideal.Quotient.mk (Ideal.span {(p : S)}) a)
  refine ⟨q, Ideal.Quotient.eq.mp ?_⟩
  rw [PreTilt.mk_untilt_eq_coeff_zero]
  exact hq

/-- pがπ^Nの単元倍（N>1）なら、πの単元倍はtiltのuntiltとして選べる。
誤差が p の倍であることと、p 進完備性から π が Jacobson 根基に入ることを使う。 -/
theorem exists_untilt_unit_mul_of_power
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (π : S) (u : Sˣ) (N : ℕ) (hN : 1 < N) (hpEq : (p : S) = u * π ^ N) :
    ∃ (q : PreTilt S p) (v : Sˣ), q.untilt = v * π := by
  obtain ⟨q, hq⟩ := exists_untilt_eq_mod_p S p hF π
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hq
  have hpJac : (p : S) ∈ (⊥ : Ideal S).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(p : S)})
      (Ideal.subset_span (Set.mem_singleton _))
  have hπpow : π ^ N ∈ (⊥ : Ideal S).jacobson := by
    rw [hpEq] at hpJac
    simpa [mul_assoc] using (⊥ : Ideal S).jacobson.mul_mem_left (↑(u⁻¹) : S) hpJac
  have hπ : π ∈ (⊥ : Ideal S).jacobson :=
    Ideal.isRadical_jacobson (⊥ : Ideal S) (Ideal.mem_radical_iff.mpr ⟨N, hπpow⟩)
  have hpositive : 0 < N - 1 := Nat.sub_pos_of_lt hN
  have hunit : IsUnit (1 + (u : S) * π ^ (N - 1) * a) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    simpa only [add_sub_cancel_left] using
      (⊥ : Ideal S).jacobson.mul_mem_right a
        ((⊥ : Ideal S).jacobson.mul_mem_left (u : S)
          (Ideal.pow_mem_of_mem _ hπ (N - 1) hpositive))
  obtain ⟨v, hv⟩ := hunit
  refine ⟨q, v, ?_⟩
  have hpower : π ^ (N - 1) * π = π ^ N := by
    rw [← pow_succ]
    congr 1
    exact Nat.sub_add_cancel (Nat.le_of_lt hN)
  rw [← hpower] at hpEq
  rw [hpEq] at ha
  rw [hv]
  linear_combination ha

/-- p乗根の場合の互換入口。一般の指数N>1の補題に帰着する。 -/
theorem exists_untilt_unit_mul
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (π : S) (u : Sˣ) (hpEq : (p : S) = u * π ^ p) :
    ∃ (q : PreTilt S p) (v : Sˣ), q.untilt = v * π :=
  exists_untilt_unit_mul_of_power S p hF π u p (Fact.out : p.Prime).one_lt hpEq

/-- 単項核を仮定せず、単元係数を持つ特別なFontaine核の元を選ぶ。 -/
theorem exists_untilt_unit_mul_and_unit_coefficient_primitive_kernel
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (π : S) (u : Sˣ) (hpEq : (p : S) = u * π ^ p) :
    ∃ (q : PreTilt S p) (v : Sˣ) (a : WittVector p (PreTilt S p)),
      q.untilt = v * π ∧ IsUnit (a.coeff 0) ∧
      (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a ∈
        RingHom.ker (WittVector.fontaineTheta S p) := by
  obtain ⟨q, v, hq⟩ := exists_untilt_unit_mul S p hF π u hpEq
  let w : Sˣ := u * (v⁻¹) ^ p
  have hpq : (p : S) = (w : S) * q.untilt ^ p := by
    rw [hq, mul_pow, hpEq]
    change (u : S) * π ^ p =
      ((u : S) * (↑(v⁻¹) : S) ^ p) * ((v : S) ^ p * π ^ p)
    calc
      _ = (u : S) * (((↑(v⁻¹) : S) * (v : S)) ^ p * π ^ p) := by simp
      _ = _ := by simp only [mul_pow]; ring
  obtain ⟨a, ha⟩ := surjective_fontaineTheta hF (-(w : S))
  have ha0 : IsUnit (a.coeff 0) := by
    apply perfection_isUnit_of_coeff_zero (ModP S p) p
    change IsUnit (PreTilt.coeff 0 (a.coeff 0))
    rw [← WittVector.mk_fontaineTheta, ha]
    exact (w.isUnit.neg).map (Ideal.Quotient.mk (Ideal.span {(p : S)}))
  have hξ : (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a ∈
      RingHom.ker (WittVector.fontaineTheta S p) := by
    change WittVector.fontaineTheta S p _ = 0
    rw [map_add, map_natCast, map_mul, map_pow, WittVector.fontaineTheta_teichmuller, ha, hpq]
    ring
  exact ⟨q, v, a, hq, ha0, hξ⟩

/-- 単元係数を明示したFontaine核の生成元。ねじれ元のTeichmuller表示に用いる。 -/
theorem exists_untilt_unit_mul_and_unit_coefficient_kernel_generator
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (π : S) (u : Sˣ) (hpEq : (p : S) = u * π ^ p) :
    ∃ (q : PreTilt S p) (v : Sˣ) (a : WittVector p (PreTilt S p)),
      q.untilt = v * π ∧ IsUnit (a.coeff 0) ∧
      RingHom.ker (WittVector.fontaineTheta S p) =
        Ideal.span {(p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a} := by
  obtain ⟨q, v, a, hq, ha0, hξ⟩ :=
    exists_untilt_unit_mul_and_unit_coefficient_primitive_kernel S p hF π u hpEq
  have hπpow : π ^ p ∈ Ideal.span {(p : S)} := by
    have hm : (u : S) * π ^ p ∈ Ideal.span {(p : S)} := by
      rw [← hpEq]
      exact Ideal.subset_span (Set.mem_singleton _)
    simpa [mul_assoc] using (Ideal.span {(p : S)}).mul_mem_left (↑(u⁻¹) : S) hm
  have hqpow : q.untilt ^ p ∈ Ideal.span {(p : S)} := by
    rw [hq, mul_pow]
    exact (Ideal.span {(p : S)}).mul_mem_left _ hπpow
  exact ⟨q, v, a, hq, ha0, ker_fontaineTheta_eq_span_primitive_shape S p hker q a hqpow hξ⟩

/-- 四条件に現れる Frobenius 全射性、単項核、p=unit·π^p から、実際の compatible roots
をもつ π の単元倍と、Fontaine 核を生成する `p+[q]^p x` を同時に選べる。
BMS 判定の核の生成元同定までを、被約性や Frobenius 単射性を仮定せずに供給する。 -/
theorem exists_untilt_unit_mul_and_kernel_generator
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (π : S) (u : Sˣ) (hpEq : (p : S) = u * π ^ p) :
    ∃ (q : PreTilt S p) (v : Sˣ) (x : WittVector p (PreTilt S p)),
      q.untilt = v * π ∧ RingHom.ker (WittVector.fontaineTheta S p) =
        Ideal.span {(p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * x} := by
  obtain ⟨q, v, a, hq, _, hgen⟩ :=
    exists_untilt_unit_mul_and_unit_coefficient_kernel_generator S p hF hker π u hpEq
  exact ⟨q, v, a, hq, hgen⟩

end Fontaine
end SerrePositivity.PerfectoidFrobeniusCriterion

end PerfectoidFrobeniusCriterionPart

section PerfectoidCharacteristicPPart

namespace SerrePositivity
open MvPolynomial

/-- 標数 p では、単項な Fontaine 核は p 自身で生成される。 -/
theorem ker_fontaineTheta_eq_span_p_of_charP
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p))} := by
  let K := RingHom.ker (WittVector.fontaineTheta S p)
  let : K.IsPrincipal := hker
  let ξ : WittVector p (PreTilt S p) := Submodule.IsPrincipal.generator K
  have hgen : Ideal.span {ξ} = K := Ideal.span_singleton_generator K
  have hξ : ξ ∈ K := Submodule.IsPrincipal.generator_mem K
  have hp : (p : WittVector p (PreTilt S p)) ∈ K := by
    simp [K, RingHom.mem_ker, CharP.cast_eq_zero]
  have hdiv : ξ ∣ (p : WittVector p (PreTilt S p)) := by
    apply Ideal.mem_span_singleton.mp
    rwa [hgen]
  obtain ⟨a, ha⟩ := hdiv
  have hzero : ξ.coeff 0 * a.coeff 0 = 0 := by
    have hh := congrArg (fun z : WittVector p (PreTilt S p) => z.coeff 0) ha
    simpa [WittVector.mul_coeff_zero, WittVector.coeff_p_zero] using hh.symm
  have hsplit : ξ.coeff 0 ^ p * a.coeff 1 + ξ.coeff 1 * a.coeff 0 ^ p = 1 := by
    have hh := congrArg (fun z : WittVector p (PreTilt S p) => z.coeff 1) ha
    simpa [witt_mul_coeff_one, WittVector.coeff_p_one, CharP.cast_eq_zero] using hh.symm
  have hproj : PreTilt.coeff 0 (ξ.coeff 0) = 0 := by
    rw [← WittVector.mk_fontaineTheta]
    have hh : WittVector.fontaineTheta S p ξ = 0 := hξ
    rw [hh, map_zero]
  have haunit : IsUnit (a.coeff 0) :=
    isUnit_of_coefficient_equations (PreTilt.coeff 0)
      (fun e he hz => perfection_idempotent_eq_zero_of_coeff_zero (ModP S p) p e he hz)
      (ξ.coeff 0) (a.coeff 0) (a.coeff 1) (ξ.coeff 1) p
      (Fact.out : p.Prime).pos hzero hsplit hproj
  have hξzero : ξ.coeff 0 = 0 := by
    exact haunit.mul_right_eq_zero.mp (by simpa only [mul_comm] using hzero)
  apply le_antisymm
  · change K ≤ _
    rw [← hgen]
    apply Ideal.span_le.mpr
    rw [Set.singleton_subset_iff]
    exact (WittVector.mem_span_p_iff_coeff_zero_eq_zero ξ).mpr hξzero
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp)

/-- 標数 p の整 perfectoid 環の Frobenius は全単射。
単項核の仮定から実際に θ の核=(p) を導き、W(tilt)/(p)≃tilt を利用する。 -/
theorem IsIntegralPerfectoid.perfectRing_of_charP
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    (hS : IsIntegralPerfectoid S p) : PerfectRing S p := by
  rcases hS with hsub | ⟨hp, hc, _, hF, hker⟩
  · let : Subsingleton S := hsub
    exact ⟨⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ x⟩⟩⟩
  · let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    let := hc
    have hθ : Function.Surjective (WittVector.fontaineTheta S p) :=
      surjective_fontaineTheta hF
    have hK := ker_fontaineTheta_eq_span_p_of_charP S p hker
    let E : PreTilt S p ≃+* S :=
      (WittVector.quotientPEquiv).symm.trans
        ((Ideal.quotEquivOfEq hK.symm).trans (RingHom.quotientKerEquivOfSurjective hθ))
    refine ⟨⟨?_, ?_⟩⟩
    · intro x y hxy
      apply E.symm.injective
      apply injective_pow_p (PreTilt S p) p
      simpa only [← map_pow] using congrArg E.symm hxy
    · intro x
      obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := PreTilt S p) (p := p)).2 (E.symm x)
      refine ⟨E y, ?_⟩
      change y ^ p = E.symm x at hy
      change (E y) ^ p = x
      rw [← map_pow, hy, E.apply_symm_apply]

/-- 標数 p の整 perfectoid 環は被約。完全性を追加仮定とせず、四条件から導く。 -/
theorem IsIntegralPerfectoid.isReduced_of_charP
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    (hS : IsIntegralPerfectoid S p) : IsReduced S := by
  let := hS.perfectRing_of_charP S p
  exact isReduced_of_perfectPower S p (Fact.out : p.Prime).one_lt

/-- p=0 の整 perfectoid 環は被約。標数クラスは追加仮定にせず内部で構成する。 -/
theorem IsIntegralPerfectoid.isReduced_of_p_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    (hS : IsIntegralPerfectoid S p) (hp : (p : S) = 0) : IsReduced S := by
  rcases subsingleton_or_nontrivial S with hsub | hnontrivial
  · let : Subsingleton S := hsub
    infer_instance
  · let : Nontrivial S := hnontrivial
    let : CharP S p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    exact hS.isReduced_of_charP S p

end SerrePositivity

end PerfectoidCharacteristicPPart

section PerfectoidFrobeniusKernelPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open PerfectoidFrobeniusCriterion

theorem fontaine_frobenius_kernel_of_primitive_generator
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hθ : Function.Surjective (WittVector.fontaineTheta S p))
    (π : S) (q : PreTilt S p) (v : Sˣ) (hq : q.untilt = v * π)
    (c : WittVector p (PreTilt S p))
    (hker : RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * c})
    (x : S) (hx : x ^ p ∈ Ideal.span {π ^ p}) : x ∈ Ideal.span {π} := by
  let θ := WittVector.fontaineTheta S p
  let tq := WittVector.teichmuller p q
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨w, hw⟩ := hθ x
  obtain ⟨z, hz⟩ := hθ ((↑(v⁻¹) : S) ^ p * b)
  have hdiff : w ^ p - tq ^ p * z ∈ RingHom.ker θ := by
    change θ (w ^ p - tq ^ p * z) = 0
    rw [map_sub, map_pow, hw, map_mul, map_pow]
    rw [show θ tq = q.untilt from WittVector.fontaineTheta_teichmuller q]
    rw [hz, hq, mul_pow, hb]
    have hv : (v : S) ^ p * (↑(v⁻¹) : S) ^ p = 1 := by rw [← mul_pow]; simp
    calc
      _ = π ^ p * b * (1 - (v : S) ^ p * (↑(v⁻¹) : S) ^ p) := by ring
      _ = 0 := by rw [hv, sub_self, mul_zero]
  rw [hker] at hdiff
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hdiff
  have hcoeff := congrArg (WittVector.constantCoeff : WittVector p (PreTilt S p) →+*
    PreTilt S p) ha
  have hcoeff' : w.coeff 0 ^ p - q ^ p * z.coeff 0 = q ^ p * c.coeff 0 * a.coeff 0 := by
    simpa only [map_sub, map_pow, map_mul, map_add, WittVector.constantCoeff_apply, tq,
      WittVector.coeff_p_zero, zero_add, WittVector.teichmuller_coeff_zero] using hcoeff
  have hwPow : w.coeff 0 ^ p ∈ Ideal.span {q ^ p} := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨z.coeff 0 + c.coeff 0 * a.coeff 0, ?_⟩
    linear_combination hcoeff'
  have hwq : w.coeff 0 ∈ Ideal.span {q} := by
    let e := perfectFrobeniusQuotientEquiv (PreTilt S p) p q
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    rw [map_zero, perfectFrobeniusQuotientEquiv_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hwPow
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hwq
  have hres : w - tq * WittVector.teichmuller p r ∈
      Ideal.span {(p : WittVector p (PreTilt S p))} := by
    apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
    change (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* _)
      (w - tq * WittVector.teichmuller p r) = 0
    simpa only [map_sub, map_mul, WittVector.constantCoeff_apply, tq,
      WittVector.teichmuller_coeff_zero] using sub_eq_zero.mpr hr
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hres
  have heq := congrArg θ hd
  have hqI : q.untilt ∈ Ideal.span {π} := by
    rw [hq]
    exact (Ideal.span {π}).mul_mem_left (v : S) (Ideal.subset_span (Set.mem_singleton _))
  have hpdiv : (p : S) ∈ Ideal.span {π} := by
    have hβ : (p : WittVector p (PreTilt S p)) + tq ^ p * c ∈ RingHom.ker θ := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton _)
    change θ ((p : WittVector p (PreTilt S p)) + tq ^ p * c) = 0 at hβ
    have hβ' : (p : S) + q.untilt ^ p * θ c = 0 := by
      simpa only [map_add, map_natCast, map_mul, map_pow, θ, tq,
        WittVector.fontaineTheta_teichmuller] using hβ
    have hm : q.untilt ^ p * θ c ∈ Ideal.span {π} :=
      (Ideal.span {π}).mul_mem_right _
        (Ideal.pow_mem_of_mem _ hqI p (Fact.out : p.Prime).pos)
    have hpEq : (p : S) = -(q.untilt ^ p * θ c) := eq_neg_of_add_eq_zero_left hβ'
    rw [hpEq]
    exact (Ideal.span {π}).neg_mem hm
  have heq' : x - q.untilt * r.untilt = (p : S) * θ d := by
    simpa only [map_sub, map_mul, map_natCast, θ, tq, hw,
      WittVector.fontaineTheta_teichmuller] using heq
  have hxEq : x = q.untilt * r.untilt + (p : S) * θ d := by linear_combination heq'
  rw [hxEq]
  exact (Ideal.span {π}).add_mem
    ((Ideal.span {π}).mul_mem_right _ hqI)
    ((Ideal.span {π}).mul_mem_right _ hpdiv)

/-- 整perfectoidの四条件から、単元倍のp乗根に対するFrobenius核条件を供給する。
πの正則性や環の被約性を追加の前提にしない。 -/
theorem IsIntegralPerfectoid.frobenius_kernel_of_unit_root
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (π : S) (u : Sˣ) (hpEq : (p : S) = u * π ^ p)
    (x : S) (hx : x ^ p ∈ Ideal.span {π ^ p}) : x ∈ Ideal.span {π} := by
  rcases hS with hsub | ⟨hp, hc, _, hF, hker⟩
  · rw [Subsingleton.elim x 0]
    exact Ideal.zero_mem _
  · let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    let := hc
    obtain ⟨q, v, c, hq, hgen⟩ :=
      exists_untilt_unit_mul_and_kernel_generator S p hF hker π u hpEq
    exact fontaine_frobenius_kernel_of_primitive_generator S p
      (surjective_fontaineTheta hF) π q v hq c hgen x hx

/-- compatibleなp冪根の系について、四条件から全反復Frobeniusの核を計算する。
非零のmod p商を扱うためpの非可逆性を明示し、零環の処理は別の入口へ分離する。 -/
theorem IsIntegralPerfectoid.pow_kernel_of_compatible_roots
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : S))]
    (hS : IsIntegralPerfectoid S p) (ρ : ℕ → S) (hρ₀ : ρ 0 = (p : S))
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) (x : S) :
    x ^ (p ^ n) ∈ Ideal.span {(p : S)} ↔ x ∈ Ideal.span {ρ n} := by
  have hnonzero : ¬ Subsingleton S := by
    intro hsub
    let : Subsingleton S := hsub
    apply (Fact.out : ¬ IsUnit (p : S))
    rw [Subsingleton.elim (p : S) 1]
    exact isUnit_one
  obtain ⟨_, _, _, hF, _⟩ := hS.resolve_left hnonzero
  let f := Ideal.Quotient.mk (Ideal.span {(p : S)})
  let e : ℕ → ModP S p := fun m ↦ f (ρ m)
  have he0 : e 0 = 0 := by
    dsimp only [e]
    rw [hρ₀]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have he (m : ℕ) : e (m + 1) ^ p = e m := by
    dsimp only [e]
    rw [← map_pow, hρ m]
  have hρ₁ : ρ 1 ^ p = (p : S) := (hρ 0).trans hρ₀
  have hfirst (y : ModP S p) : y ^ p = 0 ↔ y ∈ Ideal.span {e 1} := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · intro hz
      have hzmem : z ^ p ∈ Ideal.span {(p : S)} := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa only [map_pow] using hz
      have hzroot : z ∈ Ideal.span {ρ 1} :=
        hS.frobenius_kernel_of_unit_root S p (ρ 1) 1 (by simpa using hρ₁.symm) z
          (by simpa only [hρ₁] using hzmem)
      have hm := Ideal.mem_map_of_mem f hzroot
      simpa only [Ideal.map_span, Set.image_singleton] using hm
    · intro hz
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
      rw [ha, mul_pow, show (f (ρ 1)) ^ p = 0 from by
        rw [← map_pow, hρ₁]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)),
        zero_mul]
  have heq := frobenius_pow_kernel_iff_mem_span (ModP S p) p hF e he0 he hfirst n (f x)
  have hpre : f x ∈ Ideal.span {e n} ↔ x ∈ Ideal.span {ρ n} := by
    rw [show Ideal.span {e n} = (Ideal.span {ρ n}).map f from by
      rw [Ideal.map_span, Set.image_singleton]]
    change x ∈ Ideal.comap f ((Ideal.span {ρ n}).map f) ↔ _
    rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective]
    change x ∈ Ideal.span {ρ n} ⊔ RingHom.ker
      (Ideal.Quotient.mk (Ideal.span {(p : S)})) ↔ _
    rw [Ideal.mk_ker]
    have hpMem : (p : S) ∈ Ideal.span {ρ n} := by
      have hpEq : ρ n ^ (p ^ n) = (p : S) := by
        simpa only [zero_add, hρ₀] using compatibleRoots_pow p ρ hρ 0 n
      rw [← hpEq]
      exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _
        (pow_pos (Fact.out : p.Prime).pos _)
    rw [sup_eq_left.mpr ((Ideal.span {ρ n}).span_singleton_le_iff_mem.mpr hpMem)]
  rw [← map_pow, hpre] at heq
  change (Ideal.Quotient.mk (Ideal.span {(p : S)}) (x ^ (p ^ n)) = 0 ↔
    x ∈ Ideal.span {ρ n}) at heq
  simpa only [Ideal.Quotient.eq_zero_iff_mem] using heq

end SerrePositivity

end PerfectoidFrobeniusKernelPart

section PerfectoidFontainePrincipalPart

namespace SerrePositivity.PerfectoidFrobeniusCriterion
variable (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- Fontaine核の第0係数を一元で生成できれば、その元は核全体を生成する。 -/
theorem ker_fontaineTheta_eq_span_of_constantCoeff_generation
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (ξ : WittVector p (PreTilt S p)) (hξ : WittVector.fontaineTheta S p ξ = 0)
    (hgen : ∀ x : WittVector p (PreTilt S p), WittVector.fontaineTheta S p x = 0 →
      ∃ r : PreTilt S p, x.coeff 0 = ξ.coeff 0 * r) :
    RingHom.ker (WittVector.fontaineTheta S p) = Ideal.span {ξ} := by
  apply ker_eq_span_of_regular_of_mod_generator (p : WittVector p (PreTilt S p))
    (WittVector.fontaineTheta S p) (by simpa only [map_natCast] using hregular) ξ hξ
  intro x hx
  obtain ⟨r, hr⟩ := hgen x hx
  refine ⟨WittVector.teichmuller p r, ?_⟩
  apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
  change (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* _)
    (x - ξ * WittVector.teichmuller p r) = 0
  rw [map_sub, map_mul, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, hr, sub_self]

/-- tiltの第0射影の核が(q^p)なら、単元係数の特別な関係式がFontaine核を生成する。 -/
theorem ker_fontaineTheta_eq_span_of_tilt_coeff_kernel
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (q : PreTilt S p) (a : WittVector p (PreTilt S p)) (ha : IsUnit (a.coeff 0))
    (hξ : WittVector.fontaineTheta S p
      ((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a) = 0)
    (htilt : RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) =
      Ideal.span {q ^ p}) :
    RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a} := by
  apply ker_fontaineTheta_eq_span_of_constantCoeff_generation S p hregular _ hξ
  intro x hx
  have hc : x.coeff 0 ∈ RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) := by
    change PreTilt.coeff 0 (x.coeff 0) = 0
    rw [← WittVector.mk_fontaineTheta, hx, map_zero]
  rw [htilt] at hc
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hc
  obtain ⟨u, hu⟩ := ha
  refine ⟨(↑(u⁻¹) : PreTilt S p) * r, ?_⟩
  have hco : ((p : WittVector p (PreTilt S p)) +
      WittVector.teichmuller p q ^ p * a).coeff 0 = q ^ p * a.coeff 0 := by
    change (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* PreTilt S p)
      ((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a) =
      q ^ p * a.coeff 0
    rw [map_add, map_mul, map_pow, WittVector.constantCoeff_apply,
      WittVector.coeff_p_zero, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, WittVector.constantCoeff_apply, zero_add]
  rw [hco, hr, ← hu]
  simp [← mul_assoc]

/-- 逆に、単元係数のFontaine生成元からtiltの第0射影の核を計算する。
pの正則性はこの方向には必要ない。 -/
theorem tilt_coeff_kernel_eq_span_of_fontaine_generator
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (q : PreTilt S p) (a : WittVector p (PreTilt S p)) (ha : IsUnit (a.coeff 0))
    (hgen : RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a}) :
    RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) = Ideal.span {q ^ p} := by
  let θ := WittVector.fontaineTheta S p
  let ξ := (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a
  have hcoξ : ξ.coeff 0 = q ^ p * a.coeff 0 := by
    change (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* PreTilt S p) ξ = _
    dsimp only [ξ]
    rw [map_add, map_mul, map_pow, WittVector.constantCoeff_apply,
      WittVector.coeff_p_zero, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, WittVector.constantCoeff_apply, zero_add]
  apply le_antisymm
  · intro r hr
    have hr0 : PreTilt.coeff 0 r = 0 := hr
    have hu : r.untilt ∈ Ideal.span {(p : S)} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [PreTilt.mk_untilt_eq_coeff_zero, hr0]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hu
    obtain ⟨w, hw⟩ := surjective_fontaineTheta hF b
    have hm : WittVector.teichmuller p r - (p : WittVector p (PreTilt S p)) * w ∈
        RingHom.ker θ := by
      change θ (WittVector.teichmuller p r - (p : WittVector p (PreTilt S p)) * w) = 0
      rw [map_sub, map_mul, map_natCast, hw, WittVector.fontaineTheta_teichmuller, hb, sub_self]
    rw [hgen] at hm
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hm
    have hh := congrArg (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* _) hd
    have he : r = ξ.coeff 0 * d.coeff 0 := by
      simpa only [map_sub, map_mul, WittVector.constantCoeff_apply,
        WittVector.teichmuller_coeff_zero, WittVector.coeff_p_zero, zero_mul,
        sub_zero] using hh
    rw [hcoξ, mul_assoc] at he
    exact Ideal.mem_span_singleton.mpr ⟨a.coeff 0 * d.coeff 0, he⟩
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    have hξ : ξ ∈ RingHom.ker θ := by
      rw [hgen]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hz : PreTilt.coeff 0 (q ^ p * a.coeff 0) = 0 := by
      rw [← hcoξ, ← WittVector.mk_fontaineTheta]
      change Ideal.Quotient.mk (Ideal.span {(p : S)}) (θ ξ) = 0
      rw [show θ ξ = 0 from hξ, map_zero]
    change PreTilt.coeff 0 (q ^ p) = 0
    apply (ha.map (PreTilt.coeff 0)).mul_right_eq_zero.mp
    simpa only [map_mul, mul_comm] using hz

end SerrePositivity.PerfectoidFrobeniusCriterion

end PerfectoidFontainePrincipalPart

section TiltRootSeparationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable (S : Type*) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- 元の環の互換根の列へ戻した第n成分。 -/
def tiltRootEvaluation (n : ℕ) : PreTilt S p →* S :=
  (Perfection.coeffMonoidHom S p n).comp
    (Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).symm.toMonoidHom

/-- この成分のmod p像は元のtilt座標。 -/
theorem tiltRootEvaluation_mod_p (n : ℕ) (x : PreTilt S p) :
    Ideal.Quotient.mk (Ideal.span {(p : S)}) (tiltRootEvaluation S p n x) =
      PreTilt.coeff n x := by
  have h := congrArg (Perfection.coeff (ModP S p) p n)
    ((Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).apply_symm_apply x)
  exact h

/-- 第n成分のp^n乗はuntilt。 -/
theorem tiltRootEvaluation_pow (n : ℕ) (x : PreTilt S p) :
    tiltRootEvaluation S p n x ^ p ^ n = x.untilt := by
  have h := Perfection.coeffMonoidHom_pow_p_pow_self
    ((Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).symm x) n
  exact h.trans (Perfection.coeff_zero_symm_quotientMulEquiv x)

/-- 零元の全ての持ち上げ成分は零。 -/
theorem tiltRootEvaluation_zero (n : ℕ) : tiltRootEvaluation S p n 0 = 0 := by
  let z : Perfection S p := ⟨fun _ ↦ 0, fun _ ↦ by simp [zero_pow (Fact.out : p.Prime).ne_zero]⟩
  have he : Perfection.quotientMulEquiv p (Ideal.span {(p : S)}) z = (0 : PreTilt S p) := by
    apply Perfection.ext
    intro i
    exact map_zero (Ideal.Quotient.mk (Ideal.span {(p : S)}))
  have hz := (Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).symm_apply_eq.mpr he.symm
  change Perfection.coeffMonoidHom S p n
    ((Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).symm 0) = 0
  rw [hz]
  rfl

/-- pがuntilt(q)のp乗の単元倍なら、tiltはq進分離。 -/
theorem tilt_isHausdorff_of_unit_untilt_root (q : PreTilt S p) (u : Sˣ)
    (hp : (p : S) = u * q.untilt ^ p) :
    IsHausdorff (Ideal.span {q}) (PreTilt S p) := by
  constructor
  intro x hx
  have hdiv (m : ℕ) : ∃ y : PreTilt S p, q ^ m * y = x := by
    have h := SModEq.sub_mem.mp (hx m)
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
    exact (Ideal.mem_span_singleton.mp (by simpa only [sub_zero] using h)).imp
      (fun _ he ↦ he.symm)
  have hz (n : ℕ) : tiltRootEvaluation S p n x = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {(p : S)})
    intro m
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    apply SModEq.sub_mem.mpr
    simp only [sub_zero]
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨y, hy⟩ := hdiv (p ^ (n + 1) * m)
    refine ⟨(↑(u⁻¹) : S) ^ m * tiltRootEvaluation S p n y, ?_⟩
    have hr : (p : S) = u * tiltRootEvaluation S p n q ^ p ^ (n + 1) := by
      rw [pow_succ, pow_mul, tiltRootEvaluation_pow]
      exact hp
    have hh := congrArg (tiltRootEvaluation S p n) hy
    rw [map_mul, map_pow] at hh
    rw [← hh, hr, mul_pow, pow_mul]
    have hu : (u : S) ^ m * (↑(u⁻¹) : S) ^ m = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = ((u : S) ^ m * (↑(u⁻¹) : S) ^ m) *
          (tiltRootEvaluation S p n q ^ (p ^ (n + 1) * m) *
            tiltRootEvaluation S p n y) := by rw [hu]; simp [pow_mul]
      _ = _ := by ring
  apply Perfection.ext
  intro n
  change PreTilt.coeff n x = 0
  rw [← tiltRootEvaluation_mod_p S p n x, hz, map_zero]

/-- untiltが正則ならtilt元自身も正則。 -/
theorem tilt_mul_injective_of_untilt_regular (q : PreTilt S p)
    (hq : Function.Injective (fun z : S ↦ q.untilt * z)) :
    Function.Injective (fun z : PreTilt S p ↦ q * z) := by
  apply (injective_iff_map_eq_zero (LinearMap.mulLeft (PreTilt S p) q)).mpr
  intro x hx
  change q * x = 0 at hx
  have hz (n : ℕ) : tiltRootEvaluation S p n x = 0 := by
    have hreg : IsLeftRegular (tiltRootEvaluation S p n q) :=
      (IsLeftRegular.pow_iff (pow_pos (Fact.out : p.Prime).pos n)).mp
        (by rw [tiltRootEvaluation_pow]; exact hq)
    apply hreg
    change tiltRootEvaluation S p n q * tiltRootEvaluation S p n x =
      tiltRootEvaluation S p n q * 0
    rw [mul_zero, ← map_mul, hx, tiltRootEvaluation_zero]
  apply Perfection.ext
  intro n
  change PreTilt.coeff n x = 0
  rw [← tiltRootEvaluation_mod_p S p n x, hz, map_zero]

end SerrePositivity

end TiltRootSeparationPart

section WittPrincipalSeparationPart

namespace SerrePositivity
variable (k : Type*) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- 第0係数が正則でその主イデアルに関して分離なら、Witt元に関しても分離。 -/
theorem witt_isHausdorff_of_constantCoeff (d : WittVector p k)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x))
    [IsHausdorff (Ideal.span {d.coeff 0}) k] :
    IsHausdorff (Ideal.span {d}) (WittVector p k) := by
  let C : WittVector p k →+* k := WittVector.constantCoeff
  have hcoeff (x : WittVector p k) (hx : ∀ n : ℕ, d ^ n ∣ x) : x.coeff 0 = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {d.coeff 0})
    intro n
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    apply SModEq.sub_mem.mpr
    simp only [sub_zero]
    obtain ⟨z, hz⟩ := hx n
    exact Ideal.mem_span_singleton.mpr
      ⟨C z, by simpa only [map_mul, map_pow, C, WittVector.constantCoeff_apply] using congrArg C hz⟩
  have hpreg : Function.Injective (fun x : WittVector p k ↦ (p : WittVector p k) * x) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply WittVector.eq_zero_of_p_mul_eq_zero
    simpa only [sub_mul, mul_comm] using sub_eq_zero.mpr hxy
  have hdivide (x : WittVector p k) (hx : ∀ n : ℕ, d ^ n ∣ x) :
      ∃ y, (p : WittVector p k) * y = x ∧ ∀ n : ℕ, d ^ n ∣ y := by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp
      ((WittVector.mem_span_p_iff_coeff_zero_eq_zero x).mpr (hcoeff x hx))
    refine ⟨y, hy.symm, ?_⟩
    intro n
    obtain ⟨z, hz⟩ := hx n
    have hcz : z.coeff 0 = 0 := by
      have h := congrArg C hz
      change x.coeff 0 = C (d ^ n * z) at h
      rw [map_mul, map_pow, hcoeff x hx] at h
      apply (IsLeftRegular.pow n hreg)
      change d.coeff 0 ^ n * z.coeff 0 = d.coeff 0 ^ n * 0
      simpa only [mul_zero, C, WittVector.constantCoeff_apply] using h.symm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp
      ((WittVector.mem_span_p_iff_coeff_zero_eq_zero z).mpr hcz)
    refine ⟨w, hpreg ?_⟩
    change (p : WittVector p k) * y = (p : WittVector p k) * (d ^ n * w)
    rw [← hy, hz, hw]
    ring
  have hpow (n : ℕ) (x : WittVector p k) (hx : ∀ m : ℕ, d ^ m ∣ x) :
      (p : WittVector p k) ^ n ∣ x := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      obtain ⟨y, hy, hdy⟩ := hdivide x hx
      obtain ⟨z, hz⟩ := ih y hdy
      refine ⟨z, ?_⟩
      rw [← hy, hz, pow_succ']
      ring
  constructor
  intro x hx
  have hdx (n : ℕ) : d ^ n ∣ x := by
    have h := SModEq.sub_mem.mp (hx n)
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
    exact Ideal.mem_span_singleton.mp (by simpa only [sub_zero] using h)
  apply IsHausdorff.haus' (I := Ideal.span {(p : WittVector p k)})
  intro n
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  apply SModEq.sub_mem.mpr
  simpa only [sub_zero] using Ideal.mem_span_singleton.mpr (hpow n x hdx)

end SerrePositivity

end WittPrincipalSeparationPart

section PerfectoidFontaineSeparationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open PerfectoidFrobeniusCriterion
variable (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- pの根から得るprimitive形Witt元の主イデアル進分離性。 -/
theorem witt_primitive_isHausdorff_of_tilt_root (q : PreTilt S p) (u : Sˣ)
    (hp : (p : S) = u * q.untilt ^ p)
    (hq : Function.Injective (fun x : S ↦ q.untilt * x))
    (a : WittVector p (PreTilt S p)) (ha : IsUnit (a.coeff 0)) :
    IsHausdorff (Ideal.span {((p : WittVector p (PreTilt S p)) +
      WittVector.teichmuller p q ^ p * a)}) (WittVector p (PreTilt S p)) := by
  let d := (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a
  have hd : d.coeff 0 = q ^ p * a.coeff 0 := by
    change WittVector.constantCoeff d = _
    simp only [d, map_add, map_mul, map_pow, map_natCast,
      CharP.cast_eq_zero, zero_add, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  have hqreg : IsLeftRegular q := tilt_mul_injective_of_untilt_regular S p q hq
  have hdreg : IsLeftRegular (d.coeff 0) := by
    rw [hd]
    exact (IsLeftRegular.pow p hqreg).mul ha.isRegular.left
  have : IsHausdorff (Ideal.span {q}) (PreTilt S p) :=
    tilt_isHausdorff_of_unit_untilt_root S p q u hp
  have hle : Ideal.span {d.coeff 0} ≤ Ideal.span {q} := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [hd]
    apply (Ideal.span {q}).mul_mem_right
    exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self q) p (Fact.out : p.Prime).pos
  have : IsHausdorff (Ideal.span {d.coeff 0}) (PreTilt S p) := by
    constructor
    intro x hx
    apply IsHausdorff.haus' (I := Ideal.span {q})
    intro n
    exact (hx n).mono (Submodule.smul_mono_left (pow_le_pow_left' hle n))
  exact witt_isHausdorff_of_constantCoeff (PreTilt S p) p d hdreg

/-- 単元倍p乗根・Frobenius全射・単項核を明示したFontaine核進分離性。 -/
theorem fontaine_kernel_isHausdorff_of_unit_root
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (π : S) (u : Sˣ) (hp : (p : S) = u * π ^ p)
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x)) :
    IsHausdorff (RingHom.ker (WittVector.fontaineTheta S p))
      (WittVector p (PreTilt S p)) := by
  obtain ⟨q, v, a, hq, ha, hgen⟩ :=
    exists_untilt_unit_mul_and_unit_coefficient_kernel_generator S p hF hker π u hp
  have hπpow : IsLeftRegular (π ^ p) := by
    intro x y hxy
    apply hregular
    simpa only [hp, mul_assoc] using congrArg (fun z : S ↦ (u : S) * z) hxy
  have hπ : IsLeftRegular π := (IsLeftRegular.pow_iff (Fact.out : p.Prime).pos).mp hπpow
  have hqreg : IsLeftRegular q.untilt := by
    rw [hq]
    exact v.isUnit.isRegular.left.mul hπ
  have hpq : (p : S) = (u * (v⁻¹) ^ p : Sˣ) * q.untilt ^ p := by
    rw [hq, mul_pow, hp]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    have hv : (↑(v⁻¹) : S) ^ p * (v : S) ^ p = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = (u : S) * ((↑(v⁻¹) : S) ^ p * (v : S) ^ p) * π ^ p := by rw [hv]; simp
      _ = _ := by ring
  rw [hgen]
  exact witt_primitive_isHausdorff_of_tilt_root S p q (u * (v⁻¹) ^ p) hpq hqreg a ha

/-- F7：p正則な整perfectoid環のFontaine環はker θ進分離。 -/
theorem IsIntegralPerfectoid.fontaine_kernel_isHausdorff
    (hS : IsIntegralPerfectoid S p)
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x)) :
    IsHausdorff (RingHom.ker (WittVector.fontaineTheta S p))
      (WittVector p (PreTilt S p)) := by
  have hn : ¬ Subsingleton S := by
    intro hs
    have := hs
    apply (Fact.out : ¬ IsUnit (p : S))
    rw [Subsingleton.elim (p : S) 1]
    exact isUnit_one
  obtain ⟨_, _, ⟨π, u, hp⟩, hF, hker⟩ := hS.resolve_left hn
  exact fontaine_kernel_isHausdorff_of_unit_root S p hF hker π u hp hregular

end SerrePositivity

end PerfectoidFontaineSeparationPart

section CompatibleRootsTiltPart

namespace SerrePositivity
variable (S : Type*) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))]

/-- 環内の両立する根の列をmod pへ移したtiltの元。 -/
def compatibleRootsTilt (ρ : ℕ → S) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) : PreTilt S p :=
  ⟨fun n ↦ Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ n),
    fun n ↦ by rw [← map_pow, hρ]⟩

@[simp] theorem compatibleRootsTilt_coeff (ρ : ℕ → S)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    PreTilt.coeff n (compatibleRootsTilt S p ρ hρ) =
      Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ n) := rfl

/-- 両立する根のtiltのuntiltは元の初項に一致する。 -/
theorem compatibleRootsTilt_untilt [IsAdicComplete (Ideal.span {(p : S)}) S]
    (ρ : ℕ → S) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    (compatibleRootsTilt S p ρ hρ).untilt = ρ 0 := by
  apply Perfection.teichmullerFun_spec
  intro n
  refine ⟨ρ n, rfl, ?_⟩
  have hh := compatibleRoots_pow p ρ hρ 0 n
  rw [Nat.zero_add] at hh
  rw [hh]

omit [Fact (¬ IsUnit (p : S))] in
/-- pの正則性は、その両立する各根の正則性を与える。 -/
theorem compatible_p_root_regular
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    Function.Injective (fun x : S ↦ ρ n * x) := by
  have hpow : ρ n ^ (p ^ n) = (p : S) := by
    simpa only [Nat.zero_add, hρ0] using compatibleRoots_pow p ρ hρ 0 n
  apply (IsLeftRegular.pow_iff (pow_pos (Fact.out : p.Prime).pos n)).mp
  change Function.Injective (fun x : S ↦ ρ n ^ (p ^ n) * x)
  simpa only [hpow] using hregular

omit [Fact (¬ IsUnit (p : S))] in
/-- 正の段のp冪根をmod pで零化する元は、Frobeniusで消える。 -/
theorem compatible_p_root_modP_annihilator
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (n : ℕ) (z : ModP S p)
    (hz : Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ (n + 1)) * z = 0) : z ^ p = 0 := by
  have hpow : ρ (n + 1) ^ (p ^ (n + 1)) = (p : S) := by
    simpa only [Nat.zero_add, hρ0] using compatibleRoots_pow p ρ hρ 0 (n + 1)
  have hpos : 0 < p ^ (n + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hge : p ≤ p ^ (n + 1) := by
    rw [pow_succ]
    have hh := pow_pos (Fact.out : p.Prime).pos n
    nlinarith
  have hbound : p ^ (n + 1) ≤ (p ^ (n + 1) - 1) * p := by
    have hp := (Fact.out : p.Prime).two_le
    have hh : p ^ (n + 1) - 1 + 1 = p ^ (n + 1) := Nat.sub_add_cancel hpos
    nlinarith
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hza : ρ (n + 1) * a ∈ Ideal.span {(p : S)} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  have hnew : Ideal.Quotient.mk (Ideal.span {ρ (n + 1) ^ (p ^ (n + 1))}) (ρ (n + 1)) *
      Ideal.Quotient.mk _ a = 0 := by
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [hpow] using hza
  have hh := pow_eq_zero_of_mul_eq_zero_mod_regular_pow S (ρ (n + 1))
    (compatible_p_root_regular S p hregular ρ hρ0 hρ (n + 1)) _ p hpos hbound
    (Ideal.Quotient.mk _ a) hnew
  rw [← map_pow] at hh ⊢
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hh' := Ideal.Quotient.eq_zero_iff_mem.mp hh
  simpa only [hpow] using hh'

/-- pの両立する根について、最初のmod p Frobenius核からtilt射影の核を計算する。 -/
theorem compatibleRootsTilt_coeff_zero_kernel
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hker : ∀ z : ModP S p, z ^ p = 0 ↔ z ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 1)}) :
    RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) =
      Ideal.span {compatibleRootsTilt S p ρ hρ} := by
  change RingHom.ker (Perfection.coeff (ModP S p) p 0) = _
  refine perfection_coeff_zero_kernel_eq_span (ModP S p) p hF
    (compatibleRootsTilt S p ρ hρ) ?_ ?_ ?_
  · change Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 0) = 0
    rw [hρ0]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  · change ∀ z : ModP S p, z ^ p = 0 ↔ z ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 1)}
    exact hker
  · intro n z hz
    exact compatible_p_root_modP_annihilator S p hregular ρ hρ0 hρ n z hz

end SerrePositivity

end CompatibleRootsTiltPart

section CompatibleRootsPerfectoidPart

namespace SerrePositivity
variable (S : Type*) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- pの両立する根と最初のFrobenius核から、Fontaine核の生成元を明示する。 -/
theorem fontaine_kernel_eq_span_of_compatible_p_roots
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hker : ∀ z : ModP S p, z ^ p = 0 ↔ z ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 1)}) :
    RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p)) -
        WittVector.teichmuller p (compatibleRootsTilt S p (fun n ↦ ρ (n + 1))
          (fun n ↦ hρ (n + 1))) ^ p} := by
  let q := compatibleRootsTilt S p (fun n ↦ ρ (n + 1)) (fun n ↦ hρ (n + 1))
  have hqu : q.untilt = ρ 1 := compatibleRootsTilt_untilt S p _ _
  have hqp : q ^ p = compatibleRootsTilt S p ρ hρ := by
    apply Perfection.ext
    intro n
    change (Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ (n + 1))) ^ p =
      Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ n)
    rw [← map_pow, hρ]
  have htilt : RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) =
      Ideal.span {q ^ p} := by
    rw [hqp]
    exact compatibleRootsTilt_coeff_zero_kernel S p hregular hF ρ hρ0 hρ hker
  have ha : IsUnit ((-1 : WittVector p (PreTilt S p)).coeff 0) := by
    change IsUnit ((WittVector.constantCoeff : WittVector p (PreTilt S p) →+* _) (-1))
    exact isUnit_neg_one.map _
  have hξ : WittVector.fontaineTheta S p
      ((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * (-1)) = 0 := by
    rw [map_add, map_mul, map_natCast, map_pow, map_neg, map_one,
      WittVector.fontaineTheta_teichmuller, hqu, hρ 0, hρ0]
    ring
  simpa only [mul_neg_one, sub_eq_add_neg] using
    PerfectoidFrobeniusCriterion.ker_fontaineTheta_eq_span_of_tilt_coeff_kernel
      S p hregular q (-1) ha hξ htilt

/-- p進完備でp正則な環のperfectoid性を、両立する根と最初のFrobenius核から判定する。 -/
theorem isIntegralPerfectoid_of_compatible_p_roots
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hker : ∀ z : ModP S p, z ^ p = 0 ↔ z ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 1)}) :
    IsIntegralPerfectoid S p := by
  refine Or.inr ⟨Fact.out, inferInstance, ⟨ρ 1, 1, ?_⟩, hF, ?_⟩
  · simpa only [Units.val_one, one_mul, hρ0] using (hρ 0).symm
  · rw [fontaine_kernel_eq_span_of_compatible_p_roots S p hregular hF ρ hρ0 hρ hker]
    infer_instance

end SerrePositivity

end CompatibleRootsPerfectoidPart
