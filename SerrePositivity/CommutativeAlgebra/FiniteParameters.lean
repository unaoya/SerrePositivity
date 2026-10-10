module

public import SerrePositivity.CommutativeAlgebra.Multiplicity
public import SerrePositivity.CommutativeAlgebra.LocalAlgebra
public import SerrePositivity.CommutativeAlgebra.IntegralDimension
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # 有限局所拡大と商環へのパラメータの移送

局所環上の有限代数へパラメータ系を移し、商環上の有限代数の係数環を
より小さいイデアルによる商に取り替える。正則性や長さ代数は使わない。
-/

@[expose] public section

universe u

namespace SerrePositivity

open IsLocalRing

/-- 有限局所代数への拡大は、極大イデアルを根基とするイデアルを保つ。 -/
lemma radical_map_eq_maximalIdeal_of_finite
    {A : Type u} [CommRing A] [IsLocalRing A]
    (D : Type u) [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    [IsLocalHom (algebraMap A D)] (I : Ideal A) (hI : I.radical = maximalIdeal A) :
    (I.map (algebraMap A D)).radical = maximalIdeal D := by
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff (maximalIdeal.isMaximal D).isPrime).mpr
    exact (Ideal.map_mono (Ideal.le_radical.trans_eq hI)).trans
      (map_maximalIdeal_le (algebraMap A D))
  · obtain ⟨n, hn⟩ := maximalIdeal_pow_le_map_of_finite D (R := A)
    have hm : (maximalIdeal A).map (algebraMap A D) ≤
        (I.map (algebraMap A D)).radical := by
      rw [← hI]
      exact Ideal.map_radical_le _
    intro z hz
    have : z ∈ ((I.map (algebraMap A D)).radical).radical :=
      Ideal.mem_radical_iff.mpr ⟨n, hm (hn (Ideal.pow_mem_pow hz n))⟩
    simpa only [Ideal.radical_idem] using this

/-- 単射な有限局所拡大では、パラメータ系の像もパラメータ系になる。 -/
theorem IsSystemOfParameters.map_finite
    {A : Type u} [CommRing A] [IsLocalRing A]
    (D : Type u) [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D)) {h : ℕ} {z : Fin h → A}
    (hz : IsSystemOfParameters A z) :
    IsSystemOfParameters D (algebraMap A D ∘ z) := by
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hinj
  refine ⟨(ringKrullDim_eq_of_integral_of_injective A D hinj).trans hz.1, ?_⟩
  rw [Set.range_comp, ← Ideal.map_span]
  exact radical_map_eq_maximalIdeal_of_finite D _ hz.2

/-- `√(P + (x)) = m_R` と商の次元から、商環内のパラメータ系を得る。 -/
theorem isSystemOfParameters_quotient_of_radical
    {R : Type u} [CommRing R] [IsLocalRing R] (P : Ideal R) [IsLocalRing (R ⧸ P)]
    {h : ℕ} (x : Fin h → R) (hdim : ringKrullDim (R ⧸ P) = h)
    (hprimary : (P ⊔ Ideal.span (Set.range x)).radical = maximalIdeal R) :
    IsSystemOfParameters (R ⧸ P) (Ideal.Quotient.mk P ∘ x) := by
  refine ⟨hdim, ?_⟩
  have heq : (P ⊔ Ideal.span (Set.range x)).map (Ideal.Quotient.mk P) =
      Ideal.span (Set.range (Ideal.Quotient.mk P ∘ x)) := by
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, ← Set.range_comp]
  rw [← heq, ← Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact le_sup_left), hprimary]
  exact map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

/-- `I ≤ Q` なら、`R/Q` 上有限な代数に両立する有限 `R/I` 代数構造を与えられる。 -/
theorem exists_finite_quotientAlgebra
    {R : Type u} [CommRing R] (I Q : Ideal R) (hIQ : I ≤ Q)
    (T : Type u) [CommRing T] [Algebra R T] [Algebra (R ⧸ Q) T]
    [IsScalarTower R (R ⧸ Q) T] [Module.Finite (R ⧸ Q) T] :
    ∃ (_ : Algebra (R ⧸ I) T), IsScalarTower R (R ⧸ I) T ∧ Module.Finite (R ⧸ I) T := by
  let f : R ⧸ I →+* T := Ideal.Quotient.lift I (algebraMap R T) fun r hr ↦ by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ Q) T, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (hIQ hr), map_zero]
  let : Algebra (R ⧸ I) T := f.toAlgebra
  let : IsScalarTower R (R ⧸ I) T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite R T := Module.Finite.trans (R ⧸ Q) T
  exact ⟨inferInstance, inferInstance, Module.Finite.of_restrictScalars_finite R _ _⟩

end SerrePositivity
