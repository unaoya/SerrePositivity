module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Basic
public import SerrePositivity.FieldTheory.SeparableBaseChange
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationRing
public import SerrePositivity.CommutativeAlgebra.Localization.CommonModel
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # 主局所化 R[1/g]

## 概要

主局所化 R[1/g] の一般論：R[1/g] の中の主開集合 D(f) の元の写像、二つの主局所化のもとでの元の代数、有限な主被覆の分子、主開集合の外で同型な整写像から整閉整域への一意な延長、局所化代数 `awayAlgebra`（A[1/g] → B[1/g]）。有限な比較写像と台の冪の条件から、`(d)` を消さない付値環への写像の一意な延長（`finiteComparison_valuation_extension`、CLMST Prop 2.4.7 の付値の条件）。

## 方針

`awayAlgebra` は `Localization.awayMap` から作るので局所化前後の代数写像と両立する。一意な延長は一般の整閉整域で示し、付値環の版はその特殊化。

## 規約

`awayModuleMap` は Mathlib の `LocalizedModule.map (.powers g) f` の別名。`existsUnique_valuation_extension_of_integral_away_bijective` は BhattScholze が使うので名前を残す。

## 使われ方

エタールな主局所化（`Localization/EtaleAway`）、GenericEtale、CLMST の主局所化の比較、BhattScholze の付値環。
-/

@[expose] public noncomputable section

universe u v w

section AwayAlgebraPart

namespace SerrePositivity.GenericEtale

variable (A D : Type*) [CommRing A] [CommRing D] [Algebra A D]

/-- 基底環の同じ元を両側で反転した標準局所化上の代数構造。
元の代数写像を局所化した `Localization.awayMap` から構成するので、
局所化前後の代数写像と両立する。 -/
@[instance_reducible]
def awayAlgebra (g : A) :
    Algebra (Localization.Away g) (Localization.Away (algebraMap A D g)) :=
  (Localization.awayMap (algebraMap A D) g).toAlgebra

/-- 標準局所化の代数構造は、元の基底環の作用と両立する。
局所化写像が代数写像を保つことからスカラー塔を得る。 -/
theorem awayAlgebra_scalarTower (g : A) :
    let _ := awayAlgebra A D g
    IsScalarTower A (Localization.Away g) (Localization.Away (algebraMap A D g)) := by
  let := awayAlgebra A D g
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap D (Localization.Away (algebraMap A D g)) (algebraMap A D a) =
    Localization.awayMap (algebraMap A D) g (algebraMap A (Localization.Away g) a)
  simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

end SerrePositivity.GenericEtale

end AwayAlgebraPart

section PrincipalLocalizationNormalizationPart

namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- The native scalar action retains the original intermediate localization. -/
theorem principalLocalizationTower_scalarTower (g : R) (f : Localization.Away g) :
    IsScalarTower R (Localization.Away g) (Localization.Away f) := inferInstance

/-- A principal open of R[1/g] is the original principal open at g times its numerator. -/
theorem principalLocalizationTower_isLocalization (g : R) (f : Localization.Away g) :
    IsLocalization (.powers (g * (IsLocalization.Away.sec g f).1))
      (Localization.Away f) := by
  apply IsLocalization.Away.mul_of_associated (R := R) (S := Localization.Away g)
    (T := Localization.Away f) (x := g) (z := (IsLocalization.Away.sec g f).1) (y := f)
  have he : algebraMap R (Localization.Away g) (IsLocalization.Away.sec g f).1 =
      (algebraMap R (Localization.Away g) g) ^ (IsLocalization.Away.sec g f).2 * f := by
    rw [← IsLocalization.Away.sec_spec g f, map_pow, mul_comm]
  rw [he]
  exact associated_unit_mul_left f _
    ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow _)

end SerrePositivity

end PrincipalLocalizationNormalizationPart

section DoubleLocalizationTensorComparisonPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- Base change to R[1/g] equals the standard localization of the original A. -/
def originalAwayTensorEquiv (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    (Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
      Localization.Away (algebraMap R A g) := by
  letI := GenericEtale.awayAlgebra R A g
  letI : IsScalarTower R (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
    GenericEtale.awayAlgebra_scalarTower R A g
  letI : IsLocalization (Algebra.algebraMapSubmonoid A (.powers g))
      (Localization.Away (algebraMap R A g)) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  letI : Algebra.IsPushout R A (Localization.Away g)
      (Localization.Away (algebraMap R A g)) :=
    Algebra.isPushout_of_isLocalization (.powers g) (Localization.Away g) A _
  letI : Algebra.IsPushout R (Localization.Away g) A
      (Localization.Away (algebraMap R A g)) := Algebra.IsPushout.symm inferInstance
  exact Algebra.IsPushout.equiv R (Localization.Away g) A _

/-- The base change equivalence uses the original localization map on A. -/
theorem originalAwayTensorEquiv_tmul (g : R) (a : A) :
    letI := GenericEtale.awayAlgebra R A g
    originalAwayTensorEquiv R A g ((1 : Localization.Away g) ⊗ₜ[R] a) =
      algebraMap A (Localization.Away (algebraMap R A g)) a := by
  simp only [originalAwayTensorEquiv, Algebra.IsPushout.equiv_tmul, map_one, one_mul]

/-- Two localizations preserve base change from the original A, with the original scalar tower. -/
def doubleLocalizationTensorEquiv (g : R) (f : Localization.Away g) :
    letI := GenericEtale.awayAlgebra R A g
    (Localization.Away f) ⊗[R] A ≃ₐ[Localization.Away f]
      (Localization.Away f) ⊗[Localization.Away g]
        (Localization.Away (algebraMap R A g)) := by
  letI := GenericEtale.awayAlgebra R A g
  letI : IsScalarTower R (Localization.Away g) (Localization.Away f) :=
    principalLocalizationTower_scalarTower g f
  exact (Algebra.TensorProduct.cancelBaseChange R (Localization.Away g)
      (Localization.Away f) (Localization.Away f) A).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl :
      (Localization.Away f) ≃ₐ[Localization.Away f] (Localization.Away f))
      (originalAwayTensorEquiv R A g))

/-- The normalization fixes the value of every original element of A. -/
theorem doubleLocalizationTensorEquiv_tmul (g : R) (f : Localization.Away g) (a : A) :
    letI := GenericEtale.awayAlgebra R A g
    doubleLocalizationTensorEquiv R A g f ((1 : Localization.Away f) ⊗ₜ[R] a) =
      (1 : Localization.Away f) ⊗ₜ[Localization.Away g]
        algebraMap A (Localization.Away (algebraMap R A g)) a := by
  simp only [doubleLocalizationTensorEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, originalAwayTensorEquiv_tmul]
  rfl

end SerrePositivity

end DoubleLocalizationTensorComparisonPart

section IntegralAwayExtensionPart

namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 整写像 R→S が g の外で同型なら、g を零にしない整閉整域への写像は一意に S へ延長する。
終域の付値・rank・完備性や、R→S の有限性・単射性は要求しない。 -/
theorem existsUnique_extension_of_integral_away_bijective
    (R : Type u) (S : Type v) (V : Type w)
    [CommRing R] [CommRing S] [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    [Algebra R S] [Algebra R V] [Algebra.IsIntegral R S]
    (g : R) (hg : algebraMap R V g ≠ 0)
    (hiso : Function.Bijective (Localization.awayMap (algebraMap R S) g)) :
    ∃! l : S →+* V, l.comp (algebraMap R S) = algebraMap R V := by
  let K := FractionRing V
  have hgK : algebraMap R K g ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R V K]
    exact fun h => hg ((IsFractionRing.injective V K) (h.trans (map_zero _).symm))
  let a : Localization.Away g →ₐ[R] K :=
    IsLocalization.Away.liftAlgHom g (f := Algebra.ofId R K) (isUnit_iff_ne_zero.mpr hgK)
  letI : IsLocalization.Away ((Algebra.ofId R S) g)
      (Localization.Away (algebraMap R S g)) := by
    change IsLocalization.Away (algebraMap R S g) (Localization.Away (algebraMap R S g))
    infer_instance
  let e := AlgEquiv.ofBijective
    (IsLocalization.Away.mapₐ (Localization.Away g)
      (Localization.Away (algebraMap R S g)) (Algebra.ofId R S) g) hiso
  let k : S →ₐ[R] K := a.comp (e.symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S g))))
  let v : V →ₐ[R] K := IsScalarTower.toAlgHom R V K
  have hmem (s : S) : k s ∈ v.range := by
    have hi : IsIntegral V (k s) :=
      (IsIntegral.map k (Algebra.IsIntegral.isIntegral (R := R) s)).tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp hi
  let ev := AlgEquiv.ofInjective v (IsFractionRing.injective V K)
  let l : S →ₐ[R] V := ev.symm.toAlgHom.comp (k.codRestrict v.range hmem)
  refine ⟨l.toRingHom, l.comp_algebraMap, ?_⟩
  intro m hm
  have hm' (r : R) : m (algebraMap R S r) = algebraMap R V r := RingHom.congr_fun hm r
  apply RingHom.ext
  intro s
  obtain ⟨r, n, hr⟩ := Localization.awayMap_surjective_iff.mp hiso.2 s
  have h1 := congrArg m hr
  have h2 := congrArg l hr
  simp only [map_mul, map_pow, hm'] at h1
  simp only [map_mul, map_pow, l.commutes] at h2
  exact mul_left_cancel₀ (pow_ne_zero n hg) (h1.symm.trans h2)

/-- 同じ一意延長を任意の付値環に適用する。離散性・rank 1・p 完備性は要求しないので、
原典の p 完備 rank 1 付値環条件にもそのまま適用できる。 -/
theorem existsUnique_valuation_extension_of_integral_away_bijective
    (R : Type u) (S : Type v) (V : Type w)
    [CommRing R] [CommRing S] [CommRing V] [IsDomain V] [ValuationRing V]
    [Algebra R S] [Algebra R V] [Algebra.IsIntegral R S]
    (g : R) (hg : algebraMap R V g ≠ 0)
    (hiso : Function.Bijective (Localization.awayMap (algebraMap R S) g)) :
    ∃! l : S →+* V, l.comp (algebraMap R S) = algebraMap R V := by
  letI : IsIntegrallyClosed V := (ValuationRing.integers V (FractionRing V)).isIntegrallyClosed
  exact existsUnique_extension_of_integral_away_bijective R S V g hg hiso

end SerrePositivity

end IntegralAwayExtensionPart

section FiniteComparisonValuationPart

namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false

/-- KL の有限比較の元の支持条件は、原典の付値環条件を満たす。
付値環の rank・p 完備性・離散性・perfectoid 性は要求しない。 -/
theorem finiteComparison_valuation_extension
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (d : R) (q : A →ₐ[R] B) (hq : q.toRingHom.Finite)
    (hk : ∀ x, q x = 0 → ∃ n : ℕ, d ^ n • x = 0)
    (hc : ∃ n : ℕ, ∀ y : B ⧸ q.toLinearMap.range, d ^ n • y = 0)
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra A V]
    (hI : ¬ Ideal.span {algebraMap R A d} ≤ RingHom.ker (algebraMap A V)) :
    ∃! l : B →+* V, l.comp q.toRingHom = algebraMap A V := by
  letI : Algebra A B := q.toRingHom.toAlgebra
  letI : Module.Finite A B := hq
  have hd : algebraMap A V (algebraMap R A d) ≠ 0 := by
    intro hz
    apply hI
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hz
  obtain ⟨n, hn⟩ := hc
  have hiso := localizationComparison_awayMap_bijective_of_power_bounds d q hk (by
    intro y
    refine ⟨n, ?_⟩
    apply (Submodule.Quotient.mk_eq_zero q.toLinearMap.range).mp
    change q.toLinearMap.range.mkQ (d ^ n • y) = 0
    exact (q.toLinearMap.range.mkQ.map_smul (d ^ n) y).trans (hn _))
  exact existsUnique_valuation_extension_of_integral_away_bijective A B V
    (algebraMap R A d) hd hiso

end SerrePositivity

end FiniteComparisonValuationPart
