module

public import SerrePositivity.CommutativeAlgebra.FractionRingBasis
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Unramified.Field

/-! # 通常の相対微分の分数体局所化と分離性

通常のΩを局所化する。完備微分との比較はこのモジュールに含まれない。
有限性を確認してから次元0を零加群へ移し、Mathlibの分離性判定を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct

section Coefficients
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyUnramified R S]

/-- 底環の微分が零なら、係数をその底環拡大へ移しても相対微分は変わらない。 -/
def relativeDifferentialEquivOfFormallyUnramified :
    KaehlerDifferential R T ≃ₗ[T] KaehlerDifferential S T := by
  apply LinearEquiv.ofBijective (KaehlerDifferential.map R S T T)
  refine ⟨?_, KaehlerDifferential.map_surjective R S T⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

@[simp] theorem relativeDifferentialEquivOfFormallyUnramified_D (t : T) :
    relativeDifferentialEquivOfFormallyUnramified R S T (KaehlerDifferential.D R T t) =
      KaehlerDifferential.D S T t := by
  exact KaehlerDifferential.map_D R S T T t
end Coefficients

section Fields
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]

/-- 有限体拡大では、通常の相対微分が零であることと分離性が同値。 -/
theorem isSeparable_iff_subsingleton_kaehlerDifferential :
    Algebra.IsSeparable K L ↔ Subsingleton (KaehlerDifferential K L) := by
  rw [← Algebra.FormallyUnramified.iff_isSeparable]
  exact Algebra.formallyUnramified_iff K L

/-- 微分の有限性を確認した有限体拡大の次元0による分離性判定。 -/
theorem isSeparable_iff_finrank_kaehlerDifferential_eq_zero :
    Algebra.IsSeparable K L ↔ Module.finrank L (KaehlerDifferential K L) = 0 := by
  rw [Module.finrank_zero_iff, isSeparable_iff_subsingleton_kaehlerDifferential]
end Fields

section Fractions
variable (A D K L : Type*) [CommRing A] [CommRing D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [IsFractionRing A K]
  [Algebra D L] [IsFractionRing D L] [Algebra A L] [Algebra K L]
  [IsScalarTower A D L] [IsScalarTower A K L]

/-- 環の通常相対微分を分数体へ局所化し、底環も分数体に移す自然な同型。 -/
def fractionDifferentialEquiv :
    L ⊗[D] KaehlerDifferential A D ≃ₗ[L] KaehlerDifferential K L := by
  let : Algebra.FormallyEtale D L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors D)
  let : Algebra.FormallyEtale A K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A D L).trans
    (relativeDifferentialEquivOfFormallyUnramified A K L)

@[simp] theorem fractionDifferentialEquiv_tmul_D (l : L) (d : D) :
    fractionDifferentialEquiv A D K L (l ⊗ₜ[D] KaehlerDifferential.D A D d) =
      l • KaehlerDifferential.D K L (algebraMap D L d) := by
  simp [fractionDifferentialEquiv, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D]
end Fractions

/-- 有限整域拡大の同じ分数体作用について、局所化した相対微分の次元で分離性を判定する。 -/
theorem isSeparable_fractionRing_iff_finrank_tensorDifferential_eq_zero
    (A D K L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    [Field K] [Field L] [Algebra A D] [Module.Finite A D]
    [Algebra A K] [IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L] [IsScalarTower A D L] [IsScalarTower A K L] :
    Algebra.IsSeparable K L ↔ Module.finrank L (L ⊗[D] KaehlerDifferential A D) = 0 := by
  let : Module.Finite K L := finiteDimensional_fractionRing_of_finite A D K L
  rw [isSeparable_iff_finrank_kaehlerDifferential_eq_zero,
    ← (fractionDifferentialEquiv A D K L).finrank_eq]

/-- 指定した有限単射そのものの延長についての判定。
環と分数体の係数作用を、いずれも同じfから取る。
拡大作用は分離性の引数に直接渡し、次元評価の体自身の標準作用と区別する。 -/
theorem isSeparable_fractionRingMap_iff_finrank_tensorDifferential_eq_zero
    {A D : Type*} [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    (f : A →+* D) (hf : Function.Injective f) (hfin : f.Finite) :
    letI : Module D (FractionRing D) :=
      @Algebra.toModule _ _ _ _ (inferInstance : Algebra D (FractionRing D))
    letI : SMul D (FractionRing D) :=
      (inferInstance : Algebra D (FractionRing D)).toSMul
    letI : Algebra A D := f.toAlgebra
    letI : Module A D := @Algebra.toModule _ _ _ _ f.toAlgebra
    @Algebra.IsSeparable (FractionRing A) (FractionRing D) inferInstance inferInstance
      (fractionRingMap f hf).toAlgebra ↔
      Module.finrank (FractionRing D)
        (FractionRing D ⊗[D] KaehlerDifferential A D) = 0 := by
  let : Module D (FractionRing D) :=
    @Algebra.toModule _ _ _ _ (inferInstance : Algebra D (FractionRing D))
  let : Algebra A D := f.toAlgebra
  let : Module A D := @Algebra.toModule _ _ _ _ f.toAlgebra
  let : Module.Finite A D := hfin
  let : Algebra A (FractionRing D) := ((algebraMap D (FractionRing D)).comp f).toAlgebra
  let : SMul D (FractionRing D) := (inferInstance : Algebra D (FractionRing D)).toSMul
  let : SMul A (FractionRing D) := (inferInstance : Algebra A (FractionRing D)).toSMul
  let : IsScalarTower A D (FractionRing D) := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (FractionRing A) (FractionRing D) := (fractionRingMap f hf).toAlgebra
  let : Module (FractionRing A) (FractionRing D) := fractionRingMapModule f hf
  let : IsScalarTower A (FractionRing A) (FractionRing D) :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (fractionRingMap_algebraMap f hf a).symm)
  exact isSeparable_fractionRing_iff_finrank_tensorDifferential_eq_zero
    A D (FractionRing A) (FractionRing D)

end SerrePositivity
