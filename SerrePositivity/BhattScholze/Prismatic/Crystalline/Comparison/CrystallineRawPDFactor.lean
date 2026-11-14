module
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivision

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineRawCoordinates
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRawComparison
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPFactorial
import all SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPFactorial
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineAffineDivision
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRawComparison

/-!
# 未完備結晶模型の分冪因子

## 概要
Frobenius 差の p 除算は、頂点差の自由分冪代数と通常の多項式係数に分かれる。

## 方針
局所化内の階乗部分環を、頂点差が独立な多項式変数になる座標に移す。

## 規約
係数は第 0 頂点の通常座標と、各頂点の正の反復 δ 座標からなる。

## 使われ方
結晶模型の余分な δ 座標の Čech 因子を分離する。
-/

public noncomputable section

open scoped TensorProduct

universe u v

namespace SerrePositivity.BhattScholze.Prismatic

section ChangeCoordinates

variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
  {σ : Type u} (e : A ≃+* B) (y : σ → A)
  (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
  (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))

omit [Fact p.Prime] in
private theorem factorialSubring_primeRegular (x : σ → A) :
    Function.Injective (fun v : pDivisionFactorialSubring p x =>
      (p : pDivisionFactorialSubring p x) * v) := by
  intro v w h
  apply Subtype.ext
  have hp : IsUnit (p : Localization.Away (p : A)) := by
    rw [← map_natCast (algebraMap A (Localization.Away (p : A)))]
    exact IsLocalization.Away.algebraMap_isUnit (p : A)
  exact hp.mul_left_cancel (congrArg Subtype.val h)

private def factorialCoordinateEquiv :
    pDivisionFactorialSubring p y ≃+* pDivisionFactorialSubring p (fun s => e (y s)) := by
  let z := fun s => e (y s)
  have h : (fun s => e.symm (z s)) = y := funext fun s => e.symm_apply_apply (y s)
  let f := pDivisionFactorialMap hA e.toRingHom y
  let g := (RingEquiv.subringCongr (congrArg (pDivisionFactorialSubring p) h)).toRingHom.comp
    (pDivisionFactorialMap hB e.symm.toRingHom z)
  have hf (a : A) : f (pDivisionFactorialBase p y a) = pDivisionFactorialBase p z (e a) :=
    DFunLike.congr_fun (pDivisionFactorialMap_comp_base hA e.toRingHom y) a
  have hg (b : B) : g (pDivisionFactorialBase p z b) = pDivisionFactorialBase p y (e.symm b) := by
    apply Subtype.ext
    exact pDivisionFactorialAwayMap_coeff e.symm.toRingHom b
  refine RingEquiv.ofRingHom f g ?_ ?_
  · apply pDivisionFactorialHom_ext_of_p_regular hB
    · intro m hm
      simpa only [map_natCast] using (hB m hm).map (pDivisionFactorialBase p z)
    · exact factorialSubring_primeRegular z
    · intro b
      change f (g (pDivisionFactorialBase p z b)) = _
      rw [hg, hf, e.apply_symm_apply]
      rfl
  · apply pDivisionFactorialHom_ext_of_p_regular hA
    · intro m hm
      simpa only [map_natCast] using (hA m hm).map (pDivisionFactorialBase p y)
    · exact factorialSubring_primeRegular y
    · intro a
      change g (f (pDivisionFactorialBase p y a)) = _
      rw [hf, hg, e.symm_apply_apply]
      rfl

end ChangeCoordinates

variable (p : ℕ) [Fact p.Prime] (r n : ℕ)

local notation "Z" => crystallineBasePrism p
local notation "K" => crystallineBase p
local notation "Idx" => AffineIndex r n
local notation "B" => RelativeFreeDeltaRing (R := K) Idx
local notation "DS" => relativeFreeDeltaStructure Idx (OrientedPrism.deltaStructure Z)

private theorem crystallineBase_primeLocal (m : ℕ) (hm : ¬p ∣ m) :
    IsUnit (m : crystallineBase.{u} p) := by
  have h : IsUnit (m : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hm))
  simpa only [map_natCast] using h.map
    (ULift.ringEquiv.symm : ℤ_[p] ≃+* crystallineBase.{u} p)

private theorem crystallinePolynomial_primeLocal (I : Type v) (m : ℕ) (hm : ¬p ∣ m) :
    IsUnit (m : MvPolynomial I (crystallineBase.{u} p)) := by
  simpa only [map_natCast] using (crystallineBase_primeLocal.{u} p m hm).map
    (MvPolynomial.C : crystallineBase.{u} p →+* MvPolynomial I (crystallineBase.{u} p))

private theorem rawPDCoeff_regular :
    IsRegular (p : MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n) (crystallineBase.{u} p)) := by
  let Coeff := MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n) (crystallineBase.{u} p)
  have hCoeffL : IsLeftRegular (p : Coeff) := by
    intro x y h
    have hp := (crystallineBasePrism.{u} p).generator_regular
    rw [crystallineBase_generator] at hp
    apply MvPolynomial.ext
    intro m
    apply hp
    have H := congrArg (fun f : Coeff => f.coeff m) h
    change ((p : Coeff) * x).coeff m = ((p : Coeff) * y).coeff m at H
    rw [← map_natCast (MvPolynomial.C : crystallineBase.{u} p →+* Coeff),
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul] at H
    exact H
  exact ⟨hCoeffL, fun x y h =>
    hCoeffL (((mul_comm (p : Coeff) x).trans h).trans (mul_comm y (p : Coeff)))⟩

private def rawFactorialCoordinateEquiv :
    let R := RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n)
    let E := relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure
    DeltaAdjoinDivision E (p : R) (crystallineRawPDDifference.{u} p r n) ≃+*
      pDivisionFactorialSubring p (MvPolynomial.X : ULift.{u} (Fin r × Fin n) → MvPolynomial
        (ULift.{u} (Fin r × Fin n)) (MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n)
          (crystallineBase.{u} p))) := by
  let Coeff := MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n) (crystallineBase.{u} p)
  let a := rawDifference.{u} p r n
  let b := crystallineRawPDDifference.{u} p r n
  let e := crystallineRawCoordinateEquiv (k := crystallineBase.{u} p) r n
  let f := deltaPDivisionToAway DS b
  have hp : Function.Injective (fun x : DeltaAdjoinDivision DS (p : B) b => (p : _)*x) :=
    crystallineRawPDDivision_primeRegular.{u} p r n
  let R := DeltaAdjoinDivision DS (p : B) b
  have hpR : IsRegular (p : R) := by
    refine ⟨hp, ?_⟩
    intro x y h
    apply hp
    exact ((mul_comm (p : R) x).trans h).trans (mul_comm y (p : R))
  have hloc : Function.Injective (algebraMap R (Localization.Away (p : R))) := by
    apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (p : R))
      (S := Localization.Away (p : R))).mpr
    rintro ⟨x, ⟨i, hi⟩⟩
    exact hi ▸ hpR.pow i
  have hinj : Function.Injective f := by
    intro x y h
    apply hloc
    exact ((RingHom.congr_fun (deltaPDivisionAwayToAway_comp_toAway DS b) x).symm.trans
      (congrArg (deltaPDivisionAwayToAway DS b) h)).trans
      (RingHom.congr_fun (deltaPDivisionAwayToAway_comp_toAway DS b) y)
  let f₁ := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hb : f.range = pDivisionFactorialSubring p a :=
    (pDivisionFactorialSubring_eq_raw_range
      (crystallinePolynomial_primeLocal p (AffineIndex.{u} r n × ℕ)) DS a).symm
  let f₂ := factorialCoordinateEquiv e a
    (crystallinePolynomial_primeLocal p (AffineIndex.{u} r n × ℕ))
    (fun m hm => by
      simpa only [map_natCast] using
        (crystallinePolynomial_primeLocal p (Fin r ⊕ CrystallineExtraIndex r n) m hm).map
          (MvPolynomial.C : Coeff →+* MvPolynomial (ULift.{u} (Fin r × Fin n)) Coeff))
  have he : (fun s => e (a s)) = MvPolynomial.X := funext fun s =>
    crystallineRawCoordinateEquiv_diff r n s
  let f₃ := RingEquiv.subringCongr (congrArg (pDivisionFactorialSubring p) he)
  exact f₁.trans ((RingEquiv.subringCongr hb).trans (f₂.trans f₃))

private def rawFactorialTensorEquiv :
    let Coeff := MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n) (crystallineBase.{u} p)
    (Coeff ⊗[crystallineBase.{u} p] DividedPowerAlgebra (crystallineBase.{u} p)
      (ULift.{u} (Fin r × Fin n) →₀ crystallineBase.{u} p)) ≃+*
      pDivisionFactorialSubring p (MvPolynomial.X : ULift.{u} (Fin r × Fin n) → MvPolynomial
        (ULift.{u} (Fin r × Fin n)) Coeff) :=
  freeDPFactorialTensorEquiv (ULift.{u} (Fin r × Fin n)) (crystallineBase.{u} p)
    (MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n) (crystallineBase.{u} p))
    (crystallinePolynomial_primeLocal p _) (rawPDCoeff_regular p r n)

/-- 未完備結晶模型は、通常座標の係数環と頂点差の自由分冪代数のテンソル積。 -/
def crystallineRawPDFactor :
    DeltaAdjoinDivision
        (relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure)
        (p : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n))
        (crystallineRawPDDifference.{u} p r n) ≃+*
      MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n) (crystallineBase.{u} p) ⊗[crystallineBase.{u} p]
        DividedPowerAlgebra (crystallineBase.{u} p) (ULift.{u} (Fin r × Fin n) →₀ crystallineBase.{u} p) :=
  (rawFactorialCoordinateEquiv.{u} p r n).trans (rawFactorialTensorEquiv.{u} p r n).symm

private theorem rawFactorialCoordinate_coefficient (x :
    RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n)) :
    let j := deltaAdjoinDivisionMap
      (relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure)
      (p : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n))
      (crystallineRawPDDifference.{u} p r n)
    rawFactorialCoordinateEquiv.{u} p r n (j x) =
      pDivisionFactorialBase p MvPolynomial.X (crystallineRawCoordinateEquiv r n x) := by
  apply Subtype.ext
  unfold rawFactorialCoordinateEquiv
  let e := crystallineRawCoordinateEquiv (k := crystallineBase.{u} p) r n
  let b := crystallineRawPDDifference.{u} p r n
  let D := relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure
  let j := deltaAdjoinDivisionMap D (p : B) b
  change pDivisionFactorialAwayMap p e.toRingHom (deltaPDivisionToAway D b (j x)) = _
  exact (congrArg (pDivisionFactorialAwayMap p e.toRingHom)
    (DFunLike.congr_fun (deltaPDivisionToAway_spec D b).2.1 x)).trans
      (pDivisionFactorialAwayMap_coeff e.toRingHom x)

private theorem rawPDFactor_coefficient (x :
    RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n)) :
    let j := deltaAdjoinDivisionMap
      (relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure)
      (p : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n))
      (crystallineRawPDDifference.{u} p r n)
    rawFactorialTensorEquiv.{u} p r n (crystallineRawPDFactor.{u} p r n (j x)) =
      pDivisionFactorialBase p MvPolynomial.X (crystallineRawCoordinateEquiv r n x) := by
  dsimp only
  unfold crystallineRawPDFactor
  rw [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact rawFactorialCoordinate_coefficient p r n x

private abbrev pdCoefficient (p : ℕ) [Fact p.Prime] (r n : ℕ) : Type u :=
  MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n) (crystallineBase.{u} p)

private theorem rawFactorialTensor_left (x : pdCoefficient.{u} p r n) :
    rawFactorialTensorEquiv.{u} p r n (x ⊗ₜ[crystallineBase.{u} p] 1) =
      pDivisionFactorialBase p MvPolynomial.X (MvPolynomial.C x) := by
  apply Subtype.ext
  let A := crystallineBase.{u} p
  let T := ULift.{u} (Fin r × Fin n)
  let C := pdCoefficient.{u} p r n
  let hp := rawPDCoeff_regular.{u} p r n
  let hlocal := crystallinePolynomial_primeLocal p (Fin r ⊕ CrystallineExtraIndex r n)
  let e := freeDPBaseChangeEquiv T A C
  have hx : e (x ⊗ₜ[A] 1) = algebraMap C _ x := e.commutes x
  unfold rawFactorialTensorEquiv freeDPFactorialTensorEquiv
  exact (congrArg (fun z => (freeDPFactorialEquiv T C hlocal hp z :
    Localization.Away (p : MvPolynomial T C))) hx).trans
      (freeDPFactorialEquiv_coeff T C hlocal hp x)

private theorem rawFactorialTensor_diff (t : ULift.{u} (Fin r × Fin n)) :
    rawFactorialTensorEquiv.{u} p r n
      (1 ⊗ₜ[crystallineBase.{u} p] DividedPowerAlgebra.dp (crystallineBase.{u} p) 1
        (Finsupp.single t 1)) =
      pDivisionFactorialBase p MvPolynomial.X (MvPolynomial.X t) := by
  apply Subtype.ext
  let A := crystallineBase.{u} p
  let T := ULift.{u} (Fin r × Fin n)
  let C := pdCoefficient.{u} p r n
  let hp := rawPDCoeff_regular.{u} p r n
  let hlocal := crystallinePolynomial_primeLocal p (Fin r ⊕ CrystallineExtraIndex r n)
  exact (freeDPFactorialTensorEquiv_dp T A C hlocal hp t 1).trans (by
    simp [pDivisionFactorialValue]
    rfl)

private theorem rawPDDivision_ringHom_ext {T : Type v} [CommRing T]
    (hT : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : T))
    (hpT : Function.Injective fun x : T => (p : T) * x)
    (f g : DeltaAdjoinDivision
      (relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure)
      (p : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n))
      (crystallineRawPDDifference.{u} p r n) →+* T)
    (h : ∀ x, f (deltaAdjoinDivisionMap _ _ _ x) = g (deltaAdjoinDivisionMap _ _ _ x)) :
    f = g := by
  let e := rawFactorialCoordinateEquiv.{u} p r n
  let e₀ := crystallineRawCoordinateEquiv (k := crystallineBase.{u} p) r n
  have H : f.comp e.symm.toRingHom = g.comp e.symm.toRingHom := by
    apply pDivisionFactorialHom_ext_of_p_regular
    · intro m hm
      let C := pdCoefficient.{u} p r n
      exact (map_natCast (MvPolynomial.C : C →+* MvPolynomial (ULift.{u} (Fin r × Fin n)) C) m) ▸
        (crystallinePolynomial_primeLocal p (Fin r ⊕ CrystallineExtraIndex r n) m hm).map
          (MvPolynomial.C : C →+* MvPolynomial (ULift.{u} (Fin r × Fin n)) C)
    · exact hT
    · exact hpT
    · intro x
      obtain ⟨a, rfl⟩ := e₀.surjective x
      have ha := rawFactorialCoordinate_coefficient.{u} p r n a
      change f (e.symm (pDivisionFactorialBase p MvPolynomial.X (e₀ a))) =
        g (e.symm (pDivisionFactorialBase p MvPolynomial.X (e₀ a)))
      rw [← ha, e.symm_apply_apply]
      exact h a
  apply RingHom.ext
  intro x
  have hx := DFunLike.congr_fun H (e x)
  change f (e.symm (e x)) = g (e.symm (e x)) at hx
  simpa only [RingEquiv.symm_apply_apply] using hx

end SerrePositivity.BhattScholze.Prismatic
