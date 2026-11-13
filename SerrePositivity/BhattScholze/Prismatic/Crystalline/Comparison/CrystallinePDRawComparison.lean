module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineAffineDivision
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedPushout
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineAffineDivision
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedPushout
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout

/-!
# 結晶 p 除算の未完備自由 δ 環上の表示

## 概要
自由 δ 環を先に完備化しても、その Frobenius 差を p で割る模型の剰余は変わらない。

## 方針
p 正則性と剰余での押し出しを使う。自由 δ 環の完備化単位は剰余で同型。

## 規約
p による商は可換環で取る。

## 使われ方
余分な δ 座標を未完備の多項式表示で分離する。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r n : ℕ)

private abbrev rawBase (p : ℕ) [Fact p.Prime] : Type u := crystallineBase.{u} p
private abbrev rawIndex (r n : ℕ) : Type u := AffineIndex.{u} r n
private abbrev rawPrism (p : ℕ) [Fact p.Prime] : OrientedPrism p (rawBase.{u} p) :=
  crystallineBasePrism p

local notation "Z" => rawPrism p
local notation "S" => rawIndex r n
local notation "B₀" => RelativeFreeDeltaRing (R := rawBase p) S
local notation "B" => completedFreeDelta Z S
local notation "D₀" => relativeFreeDeltaStructure S (OrientedPrism.deltaStructure Z)
local notation "D" => completedFreeDeltaStructure Z S
local notation "uB" => crystallineCompletedFreeDeltaUnit p S

/-- 未完備自由 δ 環における頂点差の Frobenius 像。 -/
def crystallineRawPDDifference (t : ULift.{u} (Fin r × Fin n)) :
    RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n) :=
  (D₀).frobeniusLift (rawDifference.{u} p r n t)

local notation "a" => crystallineRawPDDifference p r n
private abbrev frobDiff (t : ULift.{u} (Fin r × Fin n)) :
    completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r n) :=
  (D).frobeniusLift (crystallineAffineDifference.{u} p r n t)

local notation "b" => frobDiff p r n
local notation "C₀" => ClassicalDeltaDivisionCompletion D₀ (p : B₀) a
local notation "C" => ClassicalDeltaDivisionCompletion D (p : B) b

/-- 未完備自由 δ 環上で Frobenius 差の p 除算を添加した環でも p は正則。 -/
theorem crystallineRawPDDivision_primeRegular :
    let R := RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n)
    let E := relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure
    let T := DeltaAdjoinDivision E (p : R) (crystallineRawPDDifference.{u} p r n)
    IsSMulRegular T (p : T) :=
  baseChange_frobenius_primeRegular D₀ (rawDifference.{u} p r n)
    (crystallineRawFreeDelta_primeRegular p (AffineIndex.{u} r n))
    (crystallineRawFreeDeltaResidue p (AffineIndex.{u} r n))
    (rawDivision_primeRegular.{u} p r n)

private theorem unit_pddifference :
    (fun t : ULift.{u} (Fin r × Fin n) => uB (crystallineRawPDDifference.{u} p r n t)) =
      fun t : ULift.{u} (Fin r × Fin n) => (D).frobeniusLift (crystallineAffineDifference.{u} p r n t) := by
  funext t
  change uB ((D₀).frobeniusLift (rawDifference p r n t)) = _
  rw [(crystallineCompletedFreeDeltaUnit_isDeltaHom p S).map_frobeniusLift, unit_rawDifference]

private abbrev rawCompletion (p : ℕ) [Fact p.Prime] (r n : ℕ) : Type u :=
  ClassicalDeltaDivisionCompletion
    (relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure)
    (p : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n))
    (crystallineRawPDDifference.{u} p r n)

private abbrev completedModel (p : ℕ) [Fact p.Prime] (r n : ℕ) : Type u :=
  ClassicalDeltaDivisionCompletion
    (completedFreeDeltaStructure (crystallineBasePrism.{u} p) (AffineIndex.{u} r n))
    (p : completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r n))
    (frobDiff.{u} p r n)

private theorem rawToCompleted_exists :
    ∃! f : rawCompletion.{u} p r n →+* completedModel.{u} p r n,
      (classicalDeltaDivisionStructure D₀ (p : B₀) a).IsDeltaHom
        (classicalDeltaDivisionStructure D (p : B) b) f ∧
      f.comp (classicalDeltaDivisionMap D₀ (p : B₀) a) =
        (classicalDeltaDivisionMap D (p : B) b).comp uB := by
  let f := (classicalDeltaDivisionMap D (p : B) b).comp uB
  have hf : (D₀).IsDeltaHom (classicalDeltaDivisionStructure D (p : B) b) f :=
    (classicalDeltaDivisionMap_isDeltaHom D (p : B) b).comp
      (crystallineCompletedFreeDeltaUnit_isDeltaHom p S)
  have hp : f (p : B₀) = (p : C) := map_natCast f p
  have hreg : Function.Injective (fun x : C => f (p : B₀) * x) := by
    rw [hp]
    exact classicalPDivision_p_mul_injective D b
  have hdiv (t : ULift.{u} (Fin r × Fin n)) : f (p : B₀) ∣ f (a t) := by
    rw [hp]
    refine ⟨classicalPDivisionVariable D b t, ?_⟩
    change classicalDeltaDivisionMap D (p : B) b (uB (a t)) = _
    rw [show uB (a t) = b t from congrFun (unit_pddifference p r n) t]
    exact (classicalPDivisionVariable_relation D b t).symm
  let J : Ideal C := Ideal.span {(p : C)}
  let := classicalPDivision_isAdicComplete D b
  exact existsUnique_classicalDeltaDivisionHom D₀ (classicalDeltaDivisionStructure D (p : B) b)
    (p : B₀) a f hf hreg hdiv J (Ideal.subset_span rfl)
    (by rw [hp]; exact Ideal.subset_span rfl)

private def rawToCompleted : rawCompletion.{u} p r n →+* completedModel.{u} p r n := (rawToCompleted_exists.{u} p r n).choose

private theorem unit_modPrime_isIso :
    IsIso (crystallineModPrimeRingMap p
      (CommRingCat.ofHom (crystallineCompletedFreeDeltaUnit p (AffineIndex.{u} r n)))) := by
  let e₀ := crystallineRawFreeDeltaResidue p (AffineIndex.{u} r n)
  let e := crystallineCompletedFreeDeltaResidue p (AffineIndex.{u} r n)
  let v := (modPowOneEquiv (p := p) B₀).trans (e₀.trans (e.symm.trans (modPowOneEquiv (p := p) B).symm))
  let f := crystallineModPrimeRingMap p (CommRingCat.ofHom (uB))
  have h : f = v.toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply ((modPowOneEquiv (p := p) B).trans e).injective
    change e ((modPowOneEquiv (p := p) B) (Ideal.Quotient.mk _ (uB x))) =
      e ((modPowOneEquiv (p := p) B) (v (Ideal.Quotient.mk _ x)))
    change e (Ideal.Quotient.mk _ (uB x)) =
      e ((modPowOneEquiv (p := p) B) ((modPowOneEquiv (p := p) B).symm
        (e.symm (e₀ (Ideal.Quotient.mk _ x)))))
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact crystallineCompletedFreeDeltaResidue_unit p _ x
  change IsIso f
  rw [h]
  infer_instance

/-- 未完備自由 δ 環で先に p 除算しても、完備模型の剰余は同じ。 -/
def crystallinePDRawComparison (m : SimplexCategory) :
    crystallineModPrimeRing p (CommRingCat.of (ClassicalDeltaDivisionCompletion
      (relativeFreeDeltaStructure (AffineIndex.{u} r m.len) (crystallineBasePrism.{u} p).deltaStructure)
      (p : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r m.len))
      (crystallineRawPDDifference.{u} p r m.len))) ≅
      (modPrimeCosimplicial p (pdDeltaRings.{u} p r)).obj m := by
  let n := m.len
  let g := rawToCompleted.{u} p r n
  have hg := (rawToCompleted_exists.{u} p r n).choose_spec.1
  have h := crystallineCompletedDivision_modPrime_isPushout
    (relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure)
    (crystallineRawPDDifference.{u} p r n)
    (completedFreeDeltaStructure (crystallineBasePrism.{u} p) (AffineIndex.{u} r n))
    (crystallinePDDifference.{u} p r m)
    (crystallineRawPDDivision_primeRegular.{u} p r n)
    (crystallineAffineFrobeniusDivision_primeRegular.{u} p r n)
    (crystallineCompletedFreeDeltaUnit_isDeltaHom p (AffineIndex.{u} r n))
    (unit_pddifference.{u} p r n) hg.1 hg.2
  letI := unit_modPrime_isIso.{u} p r n
  let q := crystallineModPrimeRingMap p (CommRingCat.ofHom g)
  have hq : IsIso q := h.isIso_inr_of_isIso
  let e := @asIso _ _ _ _ q hq
  exact e

/-- 未完備自由 δ 環上で添加した p 除算から結晶側の完備模型への標準射。 -/
def crystallinePDRawToTarget (m : SimplexCategory) :
    let R := RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r m.len)
    let E := relativeFreeDeltaStructure (AffineIndex.{u} r m.len) (crystallineBasePrism.{u} p).deltaStructure
    DeltaAdjoinDivision E (p : R) (crystallineRawPDDifference.{u} p r m.len) →+*
      ClassicalDeltaDivisionCompletion
        (completedFreeDeltaStructure (crystallineBasePrism.{u} p) (AffineIndex.{u} r m.len))
        (p : completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r m.len))
        (crystallinePDDifference.{u} p r m) :=
  (rawToCompleted.{u} p r m.len).comp (rawToCompletion
    (relativeFreeDeltaStructure (AffineIndex.{u} r m.len) (crystallineBasePrism.{u} p).deltaStructure)
    (crystallineRawPDDifference.{u} p r m.len))

/-- 標準射は自由 δ 環からの係数写像を保つ。 -/
theorem crystallinePDRawToTarget_comp (m : SimplexCategory)
    (x : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r m.len)) :
    let R := RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r m.len)
    let E := relativeFreeDeltaStructure (AffineIndex.{u} r m.len) (crystallineBasePrism.{u} p).deltaStructure
    crystallinePDRawToTarget.{u} p r m
      (deltaAdjoinDivisionMap E (p : R) (crystallineRawPDDifference.{u} p r m.len) x) =
      pdDeltaUnit.{u} p r m (crystallineCompletedFreeDeltaUnit p (AffineIndex.{u} r m.len) x) :=
  DFunLike.congr_fun (rawToCompleted_exists.{u} p r m.len).choose_spec.1.2 x

/-- 未完備側から完備模型への標準射は mod p で同型。 -/
theorem crystallinePDRawToTarget_isIso_modPrime (m : SimplexCategory) :
    IsIso (crystallineModPrimeRingMap p (CommRingCat.ofHom (crystallinePDRawToTarget.{u} p r m))) := by
  let E := relativeFreeDeltaStructure (AffineIndex.{u} r m.len) (crystallineBasePrism.{u} p).deltaStructure
  let y := crystallineRawPDDifference.{u} p r m.len
  let e := rawToCompletion_modPrimeIso E y (crystallineRawPDDivision_primeRegular.{u} p r m.len)
  let e' := crystallinePDRawComparison.{u} p r m
  have h : e.hom ≫ e'.hom =
      crystallineModPrimeRingMap p (CommRingCat.ofHom (crystallinePDRawToTarget.{u} p r m)) := by
    have h₀ : e.hom = crystallineModPrimeRingMap p (CommRingCat.ofHom (rawToCompletion E y)) :=
      rawToCompletion_modPrimeIso_hom E y _
    have h₁ : e'.hom = crystallineModPrimeRingMap p (CommRingCat.ofHom (rawToCompleted.{u} p r m.len)) :=
      rfl
    erw [h₀, h₁, ringMap_comp]
    rfl
  let := e.isIso_hom
  let := e'.isIso_hom
  have hh : IsIso (e.hom ≫ e'.hom) := CategoryTheory.IsIso.comp_isIso
  exact h ▸ hh

end SerrePositivity.BhattScholze.Prismatic
