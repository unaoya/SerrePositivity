module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldCompletion
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-! # 超越的単生成剰余体拡大の持ち上げ

指定体K=k(a)への評価写像の核でB[X]を局所化する。
超越性から核はm_B B[X]に等しく、局所化の剰余体写像はKへの全射になる。
係数写像とXの像を保持し、Noether版は共通の完備化APIを適用する。
-/

public section
universe u
namespace SerrePositivity
open IsLocalRing Polynomial

/-- 剰余体へ係数を還元してから、指定された元で評価する。 -/
noncomputable def residuePolynomialEval
    (B : Type*) [CommRing B] [IsLocalRing B]
    {K : Type*} [Field K] [Algebra (ResidueField B) K] (a : K) : B[X] →+* K :=
  (aeval a).toRingHom.comp (Polynomial.mapRingHom (residue B))

/-- 超越的な評価の核は、基底の極大イデアルの多項式環への拡張である。 -/
theorem residuePolynomialEval_ker
    (B : Type*) [CommRing B] [IsLocalRing B]
    {K : Type*} [Field K] [Algebra (ResidueField B) K] (a : K)
    (ha : Transcendental (ResidueField B) a) :
    RingHom.ker (residuePolynomialEval B a) = (maximalIdeal B).map Polynomial.C := by
  rw [residuePolynomialEval, RingHom.ker_comp_of_injective _
    (transcendental_iff_injective.mp ha), Polynomial.ker_mapRingHom, ker_residue]

/-- 超越的な一元で生成された指定体を、平坦局所拡大の剰余体として実現する。
Noether性は要求しない。基底がNoetherなら、構成した局所化もNoetherである。 -/
theorem exists_flat_local_extension_of_transcendental_generator
    (B K : Type u) [CommRing B] [IsLocalRing B] [Field K] [Algebra (ResidueField B) K]
    (a : K) (ha : Transcendental (ResidueField B) a)
    (hgen : IntermediateField.adjoin (ResidueField B) {a} = ⊤) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra B S)
      (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (IsNoetherianRing B → IsNoetherianRing S) ∧
      (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) ∧
        ∃ s : S, e (residue S s) = a := by
  classical
  let f := residuePolynomialEval B a
  let P := RingHom.ker f
  let : P.IsPrime := RingHom.ker_isPrime f
  let S := Localization.AtPrime P
  have hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S := by
    rw [IsScalarTower.algebraMap_eq B B[X] S, ← Ideal.map_map,
      Polynomial.algebraMap_eq, ← residuePolynomialEval_ker B a ha]
    exact Localization.AtPrime.map_eq_maximalIdeal
  let : IsLocalHom (algebraMap B S) := ⟨fun b hb ↦ by
    by_contra hn
    have hm : b ∈ maximalIdeal B := hn
    have hm' := Ideal.mem_map_of_mem (algebraMap B S) hm
    rw [hmax] at hm'
    exact hm' hb⟩
  have hu (q : P.primeCompl) : IsUnit (f q) :=
    isUnit_iff_ne_zero.mpr q.property
  let g : S →+* K := IsLocalization.lift hu
  have hg : Function.Surjective g := by
    apply (IsLocalization.lift_surjective_iff hu).mpr
    intro z
    by_cases hz : z = 0
    · subst z
      exact ⟨(0, 1), by simp⟩
    obtain ⟨p, q, hzpq⟩ := (IntermediateField.mem_adjoin_simple_iff (ResidueField B) z).mp
      (hgen.symm ▸ IntermediateField.mem_top)
    obtain ⟨pB, hpB⟩ := Polynomial.map_surjective (residue B)
      (residue_surjective (R := B)) p
    obtain ⟨qB, hqB⟩ := Polynomial.map_surjective (residue B)
      (residue_surjective (R := B)) q
    have hq : aeval a q ≠ 0 := by
      intro hq
      apply hz
      rw [hzpq, hq, div_zero]
    have hqB' : qB ∈ P.primeCompl := by
      change f qB ≠ 0
      simpa [f, residuePolynomialEval, hqB] using hq
    refine ⟨(pB, ⟨qB, hqB'⟩), ?_⟩
    change z * f qB = f pB
    simp only [f, residuePolynomialEval, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      hpB, hqB]
    change z * aeval a q = aeval a p
    rw [hzpq, div_mul_cancel₀ _ hq]
  have hgker : RingHom.ker g = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g hg)
  let e : ResidueField S ≃+* K := (Ideal.quotEquivOfEq hgker.symm).trans
    (g.quotientKerEquivOfSurjective hg)
  have hev (s : S) : e (residue S s) = g s := by
    change g.quotientKerEquivOfSurjective hg
      ((Ideal.quotEquivOfEq hgker.symm) (Ideal.Quotient.mk _ s)) = _
    rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, hmax, e, ?_, algebraMap B[X] S X, ?_⟩
  · intro h
    let : IsNoetherianRing B := h
    infer_instance
  · intro x
    obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
    rw [ResidueField.map_residue, hev]
    change g (algebraMap B[X] S (C b)) = _
    rw [IsLocalization.lift_eq]
    simp [f, residuePolynomialEval]
  · rw [hev, IsLocalization.lift_eq]
    simp [f, residuePolynomialEval]

/-- Noether基底上の超越的単生成剰余体拡大の完備Noether平坦局所版。 -/
theorem exists_complete_flat_local_extension_of_transcendental_generator
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (a : K) (ha : Transcendental (ResidueField B) a)
    (hgen : IntermediateField.adjoin (ResidueField B) {a} = ⊤) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x) ∧
        ∃ c : C, e (residue C c) = a := by
  obtain ⟨S, sRing, sLocal, sAlg, sHom, sFlat, sNoeth, hmax, e, he, s, hs⟩ :=
    exists_flat_local_extension_of_transcendental_generator B K a ha hgen
  let : IsNoetherianRing S := sNoeth inferInstance
  exact exists_complete_flat_local_extension_with_residue B S K hmax e he a s hs

end SerrePositivity
