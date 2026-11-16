module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs

/-! # 絶対整閉な perfectoid 環の完備な根基商

## 概要

絶対整閉な perfectoid 環の根基イデアルでは、各元の互換根がそのイデアルに留まるので、完備な根基商は perfectoid になる（`aicPerfectoid_quotient_of_radical_and_complete`）。特にスカラーの零化イデアルによる商に当てはまる。perfectoid な零化商を元の普遍写像の検査対象にして、絶対整閉な perfectoid 環への単射があれば、全射の核の台が perfectoid 化の後も保たれることを示す。
BS 著者版 Theorem 7.14 の試験拡大に関連して、絶対整閉な perfectoid 環の根基商を扱う。

## 方針

互換根の族の完備化（BS Semiperfectoid/Surjectivity/Surjectivity）で perfectoid な商を作る。

## 規約

絶対整閉な拡大の存在は仮定も引用もしない。旧 `CommutativeAlgebra/AbsolutelyIntegrallyClosedPerfectoidQuotient`・`PerfectoidizationSupportedQuotient`。

## 使われ方

BS の Almost・Perfectoidization/Excision、CLMST。
-/

@[expose] public noncomputable section

universe u

section AbsolutelyIntegrallyClosedPerfectoidQuotientPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open _root_.SerrePositivity.BhattScholze
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]

/-- Every complete radical quotient of an absolutely integrally closed perfectoid
ring is perfectoid; no finite generation or regularity is needed. -/
theorem BhattScholze.Semiperfectoid.aicPerfectoid_quotient_of_radical_and_complete
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hAIC : _root_.SerrePositivity.IsAbsolutelyIntegrallyClosed R)
    (J : Ideal R) (hJ : J.IsRadical)
    [IsAdicComplete (Ideal.span {(p : R ⧸ J)}) (R ⧸ J)] :
    _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ J) p := by
  classical
  choose ρ hρ0 hρ using fun s : J =>
    hAIC.exists_compatible_pow_roots (Fact.out : p.Prime).pos (s : R)
  have hmem (s : J) (n : ℕ) : ρ s n ∈ J := by
    apply hJ
    refine ⟨p ^ n, ?_⟩
    have hp := _root_.SerrePositivity.compatibleRoots_pow p (ρ s) (hρ s) 0 n
    have he : ρ s n ^ (p ^ n) = (s : R) := by
      simpa only [Nat.zero_add, hρ0] using hp
    rw [he]
    exact s.property
  have hK : SerrePositivity.compatibleRootFamilyIdeal ρ = J := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨s, n⟩, rfl⟩
      exact hmem s n
    · exact (_root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyZeroIdeal_eq_of_roots_on_ideal J ρ hρ0).ge.trans
        (_root_.SerrePositivity.compatibleRootFamilyZeroIdeal_le ρ)
  have hT := _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletion_isIntegralPerfectoid hR ρ hρ
  change _root_.SerrePositivity.IsIntegralPerfectoid
    (AdicCompletion (Ideal.span {(p : R ⧸ SerrePositivity.compatibleRootFamilyIdeal ρ)})
      (R ⧸ SerrePositivity.compatibleRootFamilyIdeal ρ)) p at hT
  rw [hK] at hT
  let e : (R ⧸ J) ≃+* AdicCompletion (Ideal.span {(p : R ⧸ J)}) (R ⧸ J) :=
    RingEquiv.ofBijective (algebraMap _ _) (by
      change Function.Bijective (AdicCompletion.of _ _)
      exact AdicCompletion.of_bijective _ _)
  exact isIntegralPerfectoid_of_ringEquiv p e.symm hT

omit [Fact p.Prime] in
/-- The quotient by a scalar annihilator is complete over its own p-adic ideal. -/
theorem BhattScholze.Semiperfectoid.annihilatorPrincipalQuotient_isAdicComplete (g : R)
    [IsAdicComplete (Ideal.span {(p : R)}) R] :
    IsAdicComplete (Ideal.span {(p : R ⧸ (Ideal.span {g}).annihilator)})
      (R ⧸ (Ideal.span {g}).annihilator) := by
  have hker : (Ideal.span {g}).annihilator = LinearMap.ker (LinearMap.mulLeft R g) := by
    ext x
    rw [Submodule.mem_annihilator_span_singleton, LinearMap.mem_ker]
    change x * g = 0 ↔ g * x = 0
    rw [mul_comm]
  let : IsAdicComplete (Ideal.span {(p : R)}) (R ⧸ (Ideal.span {g}).annihilator) := by
    rw [hker]
    exact _root_.SerrePositivity.isAdicComplete_quotient_ker (Ideal.span {(p : R)}) (LinearMap.mulLeft R g)
  have hmap : (Ideal.span {(p : R)}).map
      (algebraMap R (R ⧸ (Ideal.span {g}).annihilator)) =
      Ideal.span {(p : R ⧸ (Ideal.span {g}).annihilator)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

/-- A scalar annihilator in any reduced ring is radical. -/
theorem BhattScholze.Semiperfectoid.annihilatorPrincipal_isRadical_of_reduced [IsReduced R] (g : R) :
    (Ideal.span {g}).annihilator.IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have he : g * x ^ n = 0 := by
    have hh := (Submodule.mem_annihilator_span_singleton g (x ^ n)).mp hn
    simpa only [smul_eq_mul, mul_comm] using hh
  apply (Submodule.mem_annihilator_span_singleton g x).mpr
  change x * g = 0
  rw [mul_comm]
  apply IsReduced.eq_zero
  refine ⟨n + 1, ?_⟩
  calc
    (g * x) ^ (n + 1) = g ^ n * (g * x ^ n) * x := by
      rw [mul_pow, pow_succ, pow_succ]
      ring
    _ = 0 := by rw [he]; simp

/-- The actual annihilator quotient of an absolutely integrally closed perfectoid
ring is perfectoid for every scalar, including zero and zero divisors. -/
theorem BhattScholze.Semiperfectoid.aicPerfectoid_annihilatorPrincipalQuotient
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hAIC : _root_.SerrePositivity.IsAbsolutelyIntegrallyClosed R) (g : R) :
    _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ (Ideal.span {g}).annihilator) p := by
  let := hR.isReduced R p
  let := hR.isAdicComplete R p
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.annihilatorPrincipalQuotient_isAdicComplete R p g
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.aicPerfectoid_quotient_of_radical_and_complete R p hR hAIC _
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.annihilatorPrincipal_isRadical_of_reduced R g)

end SerrePositivity

end AbsolutelyIntegrallyClosedPerfectoidQuotientPart

section PerfectoidizationSupportedQuotientPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.IsPerfectoidization
variable {A B C D E : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [CommRing E] {p : ℕ} [Fact p.Prime]
    {f : A →+* C} {g : B →+* D}

/-- If an actual surjection has a power-torsion kernel, every compatible root kills
the kernel of its actual perfectoidization comparison, detected in an injective AIC extension. -/
theorem map_kernel_roots_of_surjective_supported_kernel_of_injective_aic
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q)
    (j : C →+* E) (hj : Function.Injective j)
    (hE : IsIntegralPerfectoid E p) (hAIC : IsAbsolutelyIntegrallyClosed E)
    (ρ : ℕ → A) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, ρ 0 ^ N * a = 0) :
    ∀ n, ∀ x : C, map hf hg q x = 0 → f (ρ n) * x = 0 := by
  let := hE.isReduced E p
  intro n x hx
  have hkill (a : A) (ha : a ∈ RingHom.ker q) : j (f (ρ n)) * j (f a) = 0 := by
    obtain ⟨N, hN⟩ := hk a ha
    let J := (Ideal.span {j (f a)}).annihilator
    have hJ : J.IsRadical := _root_.SerrePositivity.BhattScholze.Semiperfectoid.annihilatorPrincipal_isRadical_of_reduced E (j (f a))
    have hbase : j (f (ρ 0)) ∈ J := by
      apply hJ
      refine ⟨N, ?_⟩
      apply (Submodule.mem_annihilator_span_singleton (j (f a)) _).mpr
      change j (f (ρ 0)) ^ N * j (f a) = 0
      simpa only [RingHom.comp_apply, map_mul, map_pow, map_zero] using congrArg (j.comp f) hN
    have hroot : j (f (ρ n)) ∈ J := by
      apply hJ
      refine ⟨p ^ n, ?_⟩
      have hpow : ρ n ^ (p ^ n) = ρ 0 := by
        simpa only [Nat.zero_add] using compatibleRoots_pow p ρ hρ 0 n
      rw [← map_pow, ← map_pow, hpow]
      exact hbase
    exact (Submodule.mem_annihilator_span_singleton (j (f a)) _).mp hroot
  let I := (Ideal.span {j (f (ρ n))}).annihilator
  let Q := E ⧸ I
  let π : E →+* Q := Ideal.Quotient.mk I
  have hQ : IsIntegralPerfectoid Q p :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.aicPerfectoid_annihilatorPrincipalQuotient E p hE hAIC (j (f (ρ n)))
  let k : A →+* Q := (π.comp j).comp f
  have hker : RingHom.ker q ≤ RingHom.ker k := by
    intro a ha
    change π (j (f a)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (Submodule.mem_annihilator_span_singleton (j (f (ρ n))) _).mpr
    change j (f a) * j (f (ρ n)) = 0
    rw [mul_comm]
    exact hkill a ha
  let b : B →+* Q := q.liftOfSurjective hq ⟨k, hker⟩
  have hb : b.comp q = k := q.liftOfSurjective_comp hq ⟨k, hker⟩
  let l : D →+* Q := hg.lift hQ b
  have hl : l.comp g = b := hg.lift_comp hQ b
  let m := map hf hg q
  have hmf : m.comp f = g.comp q := map_comp hf hg q
  have hfac : (l.comp m).comp f = k := by
    rw [RingHom.comp_assoc, hmf, ← RingHom.comp_assoc, hl, hb]
  have he : l.comp m = π.comp j :=
    (hf.lift_unique hQ k (l.comp m) hfac).trans
      (hf.lift_unique hQ k (π.comp j) rfl).symm
  have hz := RingHom.congr_fun he x
  change l (m x) = π (j x) at hz
  change m x = 0 at hx
  rw [hx, map_zero] at hz
  have hmem : j x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz.symm
  have hmul := (Submodule.mem_annihilator_span_singleton (j (f (ρ n))) (j x)).mp hmem
  apply hj
  rw [map_mul, map_zero]
  simpa only [smul_eq_mul, mul_comm] using hmul

/-- The source perfectoidization itself can serve as the absolutely integrally closed test ring. -/
theorem map_kernel_roots_of_surjective_supported_kernel_of_aic
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q) (hC : IsAbsolutelyIntegrallyClosed C)
    (ρ : ℕ → A) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, ρ 0 ^ N * a = 0) :
    ∀ n, ∀ x : C, map hf hg q x = 0 → f (ρ n) * x = 0 :=
  hf.map_kernel_roots_of_surjective_supported_kernel_of_injective_aic hg q hq
    (RingHom.id C) Function.injective_id hf.1 hC ρ hρ hk

end SerrePositivity.IsPerfectoidization

end PerfectoidizationSupportedQuotientPart
