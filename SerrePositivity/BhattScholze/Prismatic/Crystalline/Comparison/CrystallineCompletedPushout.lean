module

public import SerrePositivity.BhattScholze.Delta.Division.BaseChange
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineDivisionCompletion
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout

/-!
# 完備 p 除算の底変換の剰余

## 概要
p 正則な二つの δ 除算模型の間の底変換は、完備化の mod p でも押し出しになる。

## 方針
商を取る前の押し出しを使い、p 正則性で完備化の剰余を同定する。

## 規約
押し出しは可換環の圏で取る。

## 使われ方
結晶の橋の各次数における Frobenius 押し出し。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type u}
    (D : DeltaStructure p A) (a : σ → A)

local notation "R" => DeltaAdjoinDivision D (p : A) a
local notation "T" => DeltaDivisionTorsionQuotient D (p : A) a
local notation "C" => ClassicalDeltaDivisionCompletion D (p : A) a
local notation "DS" => deltaAdjoinDivisionStructure D (p : A) a
local notation "DT" => deltaDivisionTorsionStructure D (p : A) a
local notation "DC" => classicalDeltaDivisionStructure D (p : A) a

private def rawToCompletion : R →+* C :=
  (algebraMap T C).comp (Ideal.Quotient.mk _)

private theorem rawToCompletion_isDeltaHom : (DS).IsDeltaHom DC (rawToCompletion D a) :=
  ((DT).isDeltaHom_adicCompletion (deltaDivisionAdicIdeal D (p : A) a)
    (Ideal.subset_span (by simp))).comp
    ((DS).isDeltaHom_quotient_mk _ ((DS).isStable_deltaClosure _))

private theorem rawToCompletion_comp :
    (rawToCompletion D a).comp (deltaAdjoinDivisionMap D (p : A) a) =
      classicalDeltaDivisionMap D (p : A) a := rfl

private def modPowOneEquiv (B : Type u) [CommRing B] :
    (B ⧸ Ideal.span {(p : B) ^ (1 : ℕ)}) ≃+* (B ⧸ Ideal.span {(p : B)}) :=
  Ideal.quotEquivOfEq (congrArg (fun b : B => Ideal.span {b}) (pow_one (p : B)))

private def rawToCompletion_modPrimeIso (h : IsSMulRegular R (p : R)) :
    crystallineModPrimeRing p (CommRingCat.of R) ≅
      crystallineModPrimeRing p (CommRingCat.of C) :=
  ((modPowOneEquiv (p := p) R).trans
    ((crystallineDivisionCompletionModPrimeEquiv D a h).symm.trans
      (modPowOneEquiv (p := p) C).symm)).toCommRingCatIso

private theorem rawToCompletion_modPrimeIso_hom (h : IsSMulRegular R (p : R)) :
    (rawToCompletion_modPrimeIso D a h).hom =
      crystallineModPrimeRingMap p (CommRingCat.ofHom (rawToCompletion D a)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx := ConcreteCategory.congr_hom
    (crystallineModPrimeRingMap_comp_projection p (CommRingCat.ofHom (rawToCompletion D a))) x
  change (crystallineModPrimeRingMap p (CommRingCat.ofHom (rawToCompletion D a)))
    (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ ((rawToCompletion D a) x) at hx
  change (rawToCompletion_modPrimeIso D a h).hom (Ideal.Quotient.mk _ x) =
    (crystallineModPrimeRingMap p (CommRingCat.ofHom (rawToCompletion D a))) (Ideal.Quotient.mk _ x)
  rw [hx]
  let e := crystallineDivisionCompletionModPrimeEquiv D a h
  apply (modPowOneEquiv (p := p) C).injective
  change (modPowOneEquiv (p := p) C)
    ((modPowOneEquiv (p := p) C).symm (e.symm
      ((modPowOneEquiv (p := p) R) (Ideal.Quotient.mk _ x)))) =
    (modPowOneEquiv (p := p) C) (Ideal.Quotient.mk _ ((rawToCompletion D a) x))
  rw [RingEquiv.apply_symm_apply]
  apply e.injective
  rw [RingEquiv.apply_symm_apply]
  exact (crystallineDivisionCompletionModPrimeEquiv_unit D a h x).symm

omit [Fact p.Prime] in
private theorem ringMap_comp {B C' E : CommRingCat.{u}} (f : B ⟶ C') (g : C' ⟶ E) :
    crystallineModPrimeRingMap p f ≫ crystallineModPrimeRingMap p g =
      crystallineModPrimeRingMap p (f ≫ g) := by
  have : Epi (crystallineModPrimeProjection p B) :=
    ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  apply (cancel_epi (crystallineModPrimeProjection p B)).mp
  rw [crystallineModPrimeRingMap_comp_projection_assoc,
    crystallineModPrimeRingMap_comp_projection, crystallineModPrimeRingMap_comp_projection,
    Category.assoc]

variable {B : Type u} [CommRing B] (E : DeltaStructure p B) (b : σ → B)

private theorem completedPushout_square {f : A →+* B} (hf : D.IsDeltaHom E f)
    (hb : (fun s => f (a s)) = b)
    {k : C →+* ClassicalDeltaDivisionCompletion E (p : B) b}
    (hk : (DC).IsDeltaHom (classicalDeltaDivisionStructure E (p : B) b) k)
    (hkc : k.comp (classicalDeltaDivisionMap D (p : A) a) =
      (classicalDeltaDivisionMap E (p : B) b).comp f) :
    ∃ j : R →+* DeltaAdjoinDivision E (p : B) b,
      IsPushout (CommRingCat.ofHom f)
        (CommRingCat.ofHom (deltaAdjoinDivisionMap D (p : A) a))
        (CommRingCat.ofHom (deltaAdjoinDivisionMap E (p : B) b))
        (CommRingCat.ofHom j) ∧
      (rawToCompletion E b).comp j = k.comp (rawToCompletion D a) := by
  let Q := ClassicalDeltaDivisionCompletion E (p : B) b
  let DQ := classicalDeltaDivisionStructure E (p : B) b
  let z := (classicalDeltaDivisionMap E (p : B) b).comp f
  have hz : D.IsDeltaHom DQ z := (classicalDeltaDivisionMap_isDeltaHom E (p : B) b).comp hf
  have hzP : z (p : A) = (p : Q) := map_natCast z p
  have hr : Function.Injective (fun x : Q => z (p : A) * x) := by
    rw [hzP]
    exact classicalPDivision_p_mul_injective E b
  have ha (s : σ) : z (p : A) ∣ z (a s) := by
    rw [hzP]
    refine ⟨classicalPDivisionVariable E b s, ?_⟩
    change classicalDeltaDivisionMap E (p : B) b (f (a s)) = _
    rw [show f (a s) = b s from congrFun hb s]
    exact (classicalPDivisionVariable_relation E b s).symm
  obtain ⟨j, hj, hjd⟩ : ∃ j : R →+* DeltaAdjoinDivision E (p : B) b,
      IsPushout (CommRingCat.ofHom f)
        (CommRingCat.ofHom (deltaAdjoinDivisionMap D (p : A) a))
        (CommRingCat.ofHom (deltaAdjoinDivisionMap E (p : B) b)) (CommRingCat.ofHom j) ∧
      (deltaAdjoinDivisionStructure D (p : A) a).IsDeltaHom
        (deltaAdjoinDivisionStructure E (p : B) b) j := by
    clear ha hr hzP hz z DQ Q hkc hk k
    subst b
    let P (d : B) : Prop := ∃ j : R →+* DeltaAdjoinDivision E d (fun s => f (a s)),
      IsPushout (CommRingCat.ofHom f)
        (CommRingCat.ofHom (deltaAdjoinDivisionMap D (p : A) a))
        (CommRingCat.ofHom (deltaAdjoinDivisionMap E d (fun s => f (a s)))) (CommRingCat.ofHom j) ∧
      (deltaAdjoinDivisionStructure D (p : A) a).IsDeltaHom
        (deltaAdjoinDivisionStructure E d (fun s => f (a s))) j
    have H : P (f (p : A)) :=
      ⟨_, deltaAdjoinDivisionBaseChange_isPushout D E f hf (p : A) a,
        deltaAdjoinDivisionBaseChange_isDeltaHom D E f hf (p : A) a⟩
    exact (congrArg P (map_natCast f p)).mp H
  have hcomp : j.comp (deltaAdjoinDivisionMap D (p : A) a) =
      (deltaAdjoinDivisionMap E (p : B) b).comp f :=
    congrArg CommRingCat.Hom.hom hj.w.symm
  obtain ⟨g, _, huniq⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D DQ (p : A) a z hz hr ha
  refine ⟨j, hj, (huniq _ ⟨(rawToCompletion_isDeltaHom E b).comp hjd, ?_⟩).trans
    (huniq _ ⟨hk.comp (rawToCompletion_isDeltaHom D a), ?_⟩).symm⟩
  · rw [RingHom.comp_assoc, hcomp, ← RingHom.comp_assoc, rawToCompletion_comp]
  · rw [RingHom.comp_assoc, rawToCompletion_comp, hkc]

/-- 完備 δ 除算の Frobenius 底変換は、mod p で通常の押し出しになる。 -/
theorem crystallineCompletedDivision_modPrime_isPushout
    (hA : IsSMulRegular R (p : R))
    (hB : IsSMulRegular (DeltaAdjoinDivision E (p : B) b)
      (p : DeltaAdjoinDivision E (p : B) b))
    {f : A →+* B} (hf : D.IsDeltaHom E f) (hb : (fun s => f (a s)) = b)
    {k : C →+* ClassicalDeltaDivisionCompletion E (p : B) b}
    (hk : (DC).IsDeltaHom (classicalDeltaDivisionStructure E (p : B) b) k)
    (hkc : k.comp (classicalDeltaDivisionMap D (p : A) a) =
      (classicalDeltaDivisionMap E (p : B) b).comp f) :
    IsPushout (crystallineModPrimeRingMap p (CommRingCat.ofHom f))
      (crystallineModPrimeRingMap p (CommRingCat.ofHom (classicalDeltaDivisionMap D (p : A) a)))
      (crystallineModPrimeRingMap p (CommRingCat.ofHom (classicalDeltaDivisionMap E (p : B) b)))
      (crystallineModPrimeRingMap p (CommRingCat.ofHom k)) := by
  obtain ⟨j, hj, hcomm⟩ := completedPushout_square D a E b hf hb hk hkc
  refine (crystallineModPrime_isPushout p hj).of_iso (Iso.refl _) (Iso.refl _)
    (rawToCompletion_modPrimeIso D a hA) (rawToCompletion_modPrimeIso E b hB) ?_ ?_ ?_ ?_
  · simp
  · rw [Iso.refl_hom, Category.id_comp, rawToCompletion_modPrimeIso_hom, ringMap_comp]
    exact congrArg (fun g => crystallineModPrimeRingMap p (CommRingCat.ofHom g))
      (rawToCompletion_comp D a)
  · rw [Iso.refl_hom, Category.id_comp, rawToCompletion_modPrimeIso_hom, ringMap_comp]
    exact congrArg (fun g => crystallineModPrimeRingMap p (CommRingCat.ofHom g))
      (rawToCompletion_comp E b)
  · rw [rawToCompletion_modPrimeIso_hom, rawToCompletion_modPrimeIso_hom, ringMap_comp, ringMap_comp]
    exact congrArg (fun g => crystallineModPrimeRingMap p (CommRingCat.ofHom g)) hcomm

end SerrePositivity.BhattScholze.Prismatic
