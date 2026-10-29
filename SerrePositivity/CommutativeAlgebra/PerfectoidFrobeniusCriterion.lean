module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import SerrePositivity.CommutativeAlgebra.PerfectionIdempotents
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.Henselian

/-! # Perfectoid Frobenius 判定に使う共通部品

BMS『Integral p-adic Hodge theory』Lemma 3.10(i) の証明を、Witt ベクトルの
単元判定、Fontaine 核の特別な元の構成、perfect 環の主イデアル商の Frobenius に分ける。
これらの部品だけで四条件から判定全体を結論せず、核の生成元の同定と商の移送を分離する。
出典：https://arxiv.org/pdf/1602.03148 （印刷 pp.22–23）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
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

/-- `q.untilt^p` が p を割れば、`p+[q]^p x` という形の Fontaine 核の元が存在する。
剰余 Frobenius の全射性から既存の Fontaine 全射性を適用して係数 x を選ぶ。 -/
theorem exists_primitive_shape_mem_fontaineTheta_kernel
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (q : PreTilt S p) (hdiv : q.untilt ^ p ∣ (p : S)) :
    ∃ x : WittVector p (PreTilt S p),
      (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * x ∈
        RingHom.ker (WittVector.fontaineTheta S p) := by
  obtain ⟨c, hc⟩ := hdiv
  obtain ⟨x, hx⟩ := surjective_fontaineTheta hF (-c)
  refine ⟨x, ?_⟩
  rw [RingHom.mem_ker, map_add, map_natCast, map_mul, map_pow,
    WittVector.fontaineTheta_teichmuller, hx, hc]
  ring

/-- 定義に現れる p=unit·π^p の関係から、π の単元倍の compatible roots と
`p+[q]^p x` 型の Fontaine 核の元を同時に構成できる。
この段階では、その核の元が核全体を生成するとは主張しない。 -/
theorem exists_untilt_unit_mul_and_primitive_kernel
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (π : S) (u : Sˣ) (hpEq : (p : S) = u * π ^ p) :
    ∃ (q : PreTilt S p) (v : Sˣ) (x : WittVector p (PreTilt S p)),
      q.untilt = v * π ∧
      (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * x ∈
        RingHom.ker (WittVector.fontaineTheta S p) := by
  obtain ⟨q, v, hq⟩ := exists_untilt_unit_mul S p hF π u hpEq
  have hcancel : (v : S) ^ p * (↑(v⁻¹) : S) ^ p = 1 := by
    rw [← mul_pow]
    simp
  have hdiv : q.untilt ^ p ∣ (p : S) := by
    refine ⟨(u : S) * (↑(v⁻¹) : S) ^ p, ?_⟩
    rw [hpEq, hq, mul_pow]
    calc
      (u : S) * π ^ p = (u : S) * π ^ p * 1 := by rw [mul_one]
      _ = (u : S) * π ^ p * ((v : S) ^ p * (↑(v⁻¹) : S) ^ p) := by rw [hcancel]
      _ = _ := by ring
  obtain ⟨x, hx⟩ := exists_primitive_shape_mem_fontaineTheta_kernel S p hF q hdiv
  exact ⟨q, v, x, hq, hx⟩

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
