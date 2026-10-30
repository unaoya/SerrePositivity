module

public import SerrePositivity.FieldTheory.SeparableBaseChange
public import SerrePositivity.CommutativeAlgebra.Localization.Away
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# 整域の有限拡大の一般点でのエタール性

Noether 整域の有限拡大について、分数体の拡大が分離的なら、基底環の
非零元を一つ反転して有限エタール拡大を得る。一般点を含むエタール軌跡から
上の環の元を選び、その主イデアルを整拡大で縮約して基底環の元に置き換える。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.GenericEtale

open Algebra PrimeSpectrum

variable (A D : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
variable [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]

omit [IsDomain A] [IsNoetherianRing A] [IsDomain D] in
/-- 有限代数の両側で基底環の一元を反転すると、局所化後も有限である。
標準局所化のスカラー塔を用いて有限加群の局所化定理を適用する。 -/
theorem finite_away (g : A) :
    let _ := awayAlgebra A D g
    Module.Finite (Localization.Away g) (Localization.Away (algebraMap A D g)) := by
  let := awayAlgebra A D g
  let : IsScalarTower A (Localization.Away g) (Localization.Away (algebraMap A D g)) :=
    awayAlgebra_scalarTower A D g
  let : IsLocalization (Algebra.algebraMapSubmonoid D (Submonoid.powers g))
      (Localization.Away (algebraMap A D g)) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  exact Module.Finite.of_isLocalization A D (Submonoid.powers g)

omit [IsDomain A] [IsNoetherianRing A] [Module.Finite A D] in
/-- 両環の分数体と両立する分離拡大があれば、上の整域の一般点は
元の基底環上でエタールである。分数体は任意のモデルを選べる。
局所化と分離体拡大の形式的エタール性を合成し、零素イデアルでの局所化へ移す。 -/
theorem isEtaleAt_bot_of_separable_fractionRing
    (K L : Type u) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L]
    [IsScalarTower A D L] [IsScalarTower A K L] [Algebra.IsSeparable K L] :
    Algebra.IsEtaleAt A (⊥ : Ideal D) := by
  let : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let : Algebra.FormallyEtale A L := Algebra.FormallyEtale.comp A K L
  let : IsLocalization (nonZeroDivisors D) (Localization.AtPrime (⊥ : Ideal D)) := by
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let e : L ≃ₐ[D] Localization.AtPrime (⊥ : Ideal D) :=
    IsLocalization.algEquiv (nonZeroDivisors D) L _
  exact Algebra.FormallyEtale.of_equiv (e.restrictScalars A)

/-- Noether 整域の有限拡大が一般点でエタールなら、基底環の非零元を
一つ反転した上の環も基底環上でエタールである。
エタール軌跡の開性と、非零主イデアルの整拡大での非零縮約を使う。 -/
theorem exists_nonzero_base_etale_away_of_generic
    [Algebra.IsEtaleAt A (⊥ : Ideal D)] :
    ∃ g : A, g ≠ 0 ∧ Algebra.Etale A (Localization.Away (algebraMap A D g)) := by
  have : Algebra.FinitePresentation A D := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨f, hf, hEtale⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal D)
  have hfzero : f ≠ 0 := by simpa using hf
  let J : Ideal D := Ideal.span {f}
  have hJ : J ≠ ⊥ := by
    intro hbot
    have hmem : f ∈ J := Ideal.subset_span (by simp)
    rw [hbot, Submodule.mem_bot] at hmem
    exact hfzero hmem
  have hJA : J.under A ≠ ⊥ := Ideal.IsIntegral.under_ne_bot A hJ
  obtain ⟨g, hgJ, hgzero⟩ := (J.under A).ne_bot_iff.mp hJA
  have hg : algebraMap A D g ∈ Ideal.span {f} := hgJ
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hg
  have hopen : (basicOpen (algebraMap A D g) : Set (PrimeSpectrum D)) ⊆ basicOpen f := by
    rw [hd]
    exact basicOpen_mul_le_left f d
  have hgood : (basicOpen f : Set (PrimeSpectrum D)) ⊆ Algebra.etaleLocus A D :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hEtale
  exact ⟨g, hgzero, Algebra.basicOpen_subset_etaleLocus_iff_etale.mp (hopen.trans hgood)⟩

/-- Noether 整域の有限拡大が一般点でエタールなら、標準的な代数構造により
両環の局所化の間の写像は有限エタールとなる。
基底環の局所化もエタールなので、スカラー制限から局所化後のエタール性を得る。 -/
theorem exists_finite_etale_away_of_generic [Algebra.IsEtaleAt A (⊥ : Ideal D)] :
    ∃ g : A, g ≠ 0 ∧
      let _ := awayAlgebra A D g
      Module.Finite (Localization.Away g) (Localization.Away (algebraMap A D g)) ∧
        Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)) := by
  obtain ⟨g, hg, he⟩ := exists_nonzero_base_etale_away_of_generic A D
  let := awayAlgebra A D g
  let : IsScalarTower A (Localization.Away g) (Localization.Away (algebraMap A D g)) :=
    awayAlgebra_scalarTower A D g
  let : Algebra.Etale A (Localization.Away (algebraMap A D g)) := he
  let : Algebra.Etale A (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  exact ⟨g, hg, finite_away A D g,
    Algebra.Etale.of_restrictScalars A (Localization.Away g)
      (Localization.Away (algebraMap A D g))⟩

/-- Noether 整域の有限拡大について、両環の分数体と両立する分数体拡大が
分離的なら、基底環の非零元を一つ反転して有限エタール拡大を得る。
分数体の分離性から一般点でのエタール性を導き、エタール軌跡を使う。 -/
theorem exists_finite_etale_away_of_separable_fractionRing
    (K L : Type u) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L]
    [IsScalarTower A D L] [IsScalarTower A K L] [Algebra.IsSeparable K L] :
    ∃ g : A, g ≠ 0 ∧
      let _ := awayAlgebra A D g
      Module.Finite (Localization.Away g) (Localization.Away (algebraMap A D g)) ∧
        Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)) := by
  let : Algebra.IsEtaleAt A (⊥ : Ideal D) :=
    isEtaleAt_bot_of_separable_fractionRing A D K L
  exact exists_finite_etale_away_of_generic A D

/-- 有限単射拡大の各元の最小多項式が基底環の分数体上で分離的なら、
基底環の非零元を一つ反転して有限エタール拡大を得る。
単射性から標準分数体間の代数構造を作り、最小多項式の条件を分数体の分離性へ移す。 -/
theorem exists_finite_etale_away_of_separable_minpoly
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable) :
    ∃ g : A, g ≠ 0 ∧
      let _ := awayAlgebra A D g
      Module.Finite (Localization.Away g) (Localization.Away (algebraMap A D g)) ∧
        Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)) := by
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hinj
  let : Algebra (FractionRing A) (FractionRing D) :=
    FractionRing.liftAlgebra A (FractionRing D)
  let : Algebra.IsSeparable (FractionRing A) (FractionRing D) :=
    SerrePositivity.isSeparable_fractionRing_of_separable_minpoly
      A D (FractionRing A) (FractionRing D) hsep
  exact exists_finite_etale_away_of_separable_fractionRing
    A D (FractionRing A) (FractionRing D)

/-- 標数零の整域への有限単射拡大では、基底環の非零元を一つ反転して
有限エタール拡大を得る。分数体の拡大は代数的であり、標数零では分離的である。
局所環、完備性、正則性の仮定は不要である。 -/
theorem exists_finite_etale_away_of_charZero [CharZero D]
    (hinj : Function.Injective (algebraMap A D)) :
    ∃ g : A, g ≠ 0 ∧
      let _ := awayAlgebra A D g
      Module.Finite (Localization.Away g) (Localization.Away (algebraMap A D g)) ∧
        Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)) := by
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hinj
  let : CharZero A := (algebraMap A D).charZero
  let : CharZero (FractionRing A) := inferInstance
  let : Algebra (FractionRing A) (FractionRing D) :=
    FractionRing.liftAlgebra A (FractionRing D)
  let : Algebra.IsAlgebraic (FractionRing A) (FractionRing D) :=
    isAlgebraic_of_isFractionRing A D (FractionRing A) (FractionRing D)
  exact exists_finite_etale_away_of_separable_fractionRing
    A D (FractionRing A) (FractionRing D)

end SerrePositivity.GenericEtale
