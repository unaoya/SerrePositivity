module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineFreeDivision
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta
public import SerrePositivity.BhattScholze.Delta.Free.CrystallineTensorRegularity
public import SerrePositivity.BhattScholze.Delta.Division.BaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# affine 結晶模型の p 除算環の正則性

## 概要
Čech 頂点の差と、その Frobenius 像の p 除算は、関係式を課した段階で p 正則。

## 方針
自由な差座標の場合を示し、完備自由 δ 環と Frobenius の p 完全平坦性で移す。

## 規約
添字は第 0 頂点との差を取る。差を取る側の頂点は `Fin n` の後者。

## 使われ方
結晶比較における mod p の押し出し。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- 第 0 頂点と残りの頂点に分けた自由座標。 -/
abbrev CrystallineSplitIndex (r n : ℕ) :=
  ULift.{u} (Fin r) ⊕ ULift.{u} (Fin r × Fin n)

/-- 第 0 頂点と他の頂点による affine 座標の分解。 -/
def crystallineSplitEquiv (r n : ℕ) : CrystallineSplitIndex.{u} r n ≃ AffineIndex.{u} r n where
  toFun := Sum.elim (fun j => ⟨(j.down, 0)⟩) (fun t => ⟨(t.down.1, t.down.2.succ)⟩)
  invFun t := Fin.cases (.inl ⟨t.down.1⟩) (fun i => .inr ⟨(t.down.1, i)⟩) t.down.2
  left_inv x := by
    cases x with
    | inl j => rfl
    | inr t => obtain ⟨⟨j, i⟩⟩ := t; rfl
  right_inv x := by
    obtain ⟨⟨j, i⟩⟩ := x
    refine Fin.cases ?_ (fun k => ?_) i <;> rfl

section Unit

variable (p : ℕ) [Fact p.Prime] (Idx : Type u)

local notation "B₀" => RelativeFreeDeltaRing (R := crystallineBase p) Idx
local notation "B" => completedFreeDelta (crystallineBasePrism p) Idx
local notation "uB" => crystallineCompletedFreeDeltaUnit p Idx

private theorem completedFreeDelta_unit_completelyFlat :
    @IsCompletelyFlat B₀ inferInstance (Ideal.span {(p : B₀)}) B
      (inferInstance : CommRing B).toAddCommGroup (uB).toAlgebra.toModule := by
  let : Algebra B₀ B := (uB).toAlgebra
  have hpB : IsSMulRegular B (p : B₀) := by
    intro x y h
    apply crystallineCompletedFreeDelta_primeRegular p Idx
    change (p : B) * x = (p : B) * y
    change (p : B₀) • x = (p : B₀) • y at h
    simpa only [Algebra.smul_def, map_natCast] using h
  have hJ : (Ideal.span {(p : B₀)}).map (algebraMap B₀ B) = Ideal.span {(p : B)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let eB := (Ideal.quotEquivOfEq hJ).trans (crystallineCompletedFreeDeltaResidue p Idx)
  apply crystallineCompletelyFlat_of_freeResidue.{u} (R := B₀) (S := B) (p : B₀)
    (crystallineRawFreeDelta_primeRegular p Idx) hpB (crystallineRawFreeDeltaResidue p Idx) eB
    (RingHom.id (MvPolynomial (Idx × ℕ) (ZMod p)))
  · intro x
    change eB (Ideal.Quotient.mk _ ((uB) x)) = _
    change crystallineCompletedFreeDeltaResidue p Idx
      ((Ideal.quotEquivOfEq hJ) (Ideal.Quotient.mk _ ((uB) x))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact crystallineCompletedFreeDeltaResidue_unit p Idx x
  · exact Module.Free.self _

end Unit

section Transport

variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
  {σ : Type u} (D : DeltaStructure p A) (E : DeltaStructure p B)

omit [Fact p.Prime] in
private theorem regular_of_equiv (e : A ≃+* B) (h : IsSMulRegular A (p : A)) :
    IsSMulRegular B (p : B) := by
  intro x y hxy
  apply e.symm.injective
  apply h
  change (p : A) * e.symm x = (p : A) * e.symm y
  change (p : B) * x = (p : B) * y at hxy
  simpa only [map_mul, map_natCast] using congrArg e.symm hxy

private theorem baseChange_equiv_primeRegular (e : A ≃+* B) (he : D.IsDeltaHom E e.toRingHom)
    (a : σ → A) (b : σ → B) (hb : (fun s => e (a s)) = b)
    (ha : IsSMulRegular (DeltaAdjoinDivision D (p : A) a)
      (p : DeltaAdjoinDivision D (p : A) a)) :
    IsSMulRegular (DeltaAdjoinDivision E (p : B) b)
      (p : DeltaAdjoinDivision E (p : B) b) := by
  subst b
  let f := deltaAdjoinDivisionBaseChange D E e.toRingHom he (p : A) a
  let : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  let : IsIso (CommRingCat.ofHom f) :=
    (deltaAdjoinDivisionBaseChange_isPushout D E e.toRingHom he (p : A) a).isIso_inr_of_isIso
  have h := regular_of_equiv (asIso (CommRingCat.ofHom f)).commRingCatIsoToRingEquiv ha
  change IsSMulRegular (DeltaAdjoinDivision E (e (p : A)) (fun s => e (a s)))
    (p : DeltaAdjoinDivision E (e (p : A)) (fun s => e (a s))) at h
  rwa [map_natCast] at h

private theorem transport_primeRegular {T : Type u} [CommRing T]
    (f : A →+* B) (hf : D.IsDeltaHom E f)
    (e : B ≃+* T) (a : σ → A) {d : B} (hd : f (p : A) = d)
    (hflat : @IsCompletelyFlat A inferInstance (Ideal.span {(p : A)}) T
      (inferInstance : CommRing T).toAddCommGroup ((e.toRingHom.comp f).toAlgebra.toModule))
    (ha : IsSMulRegular (DeltaAdjoinDivision D (p : A) a)
      (p : DeltaAdjoinDivision D (p : A) a)) :
    IsSMulRegular (DeltaAdjoinDivision E d (fun s => f (a s)))
      (p : DeltaAdjoinDivision E d (fun s => f (a s))) := by
  subst d
  let N := DeltaAdjoinDivision D (p : A) a
  let F := DeltaAdjoinDivision E (f (p : A)) (fun s => f (a s))
  let k := deltaAdjoinDivisionBaseChange D E f hf (p : A) a
  let q : A →+* T := e.toRingHom.comp f
  let g : A →+* N := deltaAdjoinDivisionMap D (p : A) a
  let j : T →+* F :=
    (deltaAdjoinDivisionMap E (f (p : A)) (fun s => f (a s))).comp e.symm.toRingHom
  have h := deltaAdjoinDivisionBaseChange_isPushout D E f hf (p : A) a
  have h' : IsPushout (CommRingCat.ofHom q) (CommRingCat.ofHom g) (CommRingCat.ofHom j)
      (CommRingCat.ofHom k) := by
    apply h.of_iso (Iso.refl _) e.toCommRingCatIso (Iso.refl _) (Iso.refl _)
    · rfl
    · rfl
    · apply CommRingCat.hom_ext
      exact RingHom.ext fun x => congrArg _ (e.symm_apply_apply x).symm
    · rfl
  exact crystallinePrimeRegular_of_isPushout p q g j k h' hflat ha

private theorem baseChange_frobenius_primeRegular {ι : Type u} (a : σ → A)
    (hreg : IsSMulRegular A (p : A)) (e : (A ⧸ Ideal.span {(p : A)}) ≃+* MvPolynomial ι (ZMod p))
    (ha : IsSMulRegular (DeltaAdjoinDivision D (p : A) a)
      (p : DeltaAdjoinDivision D (p : A) a)) :
    IsSMulRegular (DeltaAdjoinDivision D (p : A) (fun s => D.frobeniusLift (a s)))
      (p : DeltaAdjoinDivision D (p : A) (fun s => D.frobeniusLift (a s))) :=
  transport_primeRegular D D D.frobeniusLift (frobeniusLift_isDeltaHom_of_regular D hreg)
    (ULift.ringEquiv.symm : A ≃+* CrystallineFrobeniusTarget D) a (map_natCast _ _)
    (crystallineCompletelyFlat_frobenius D hreg e) ha

end Transport

private theorem freeDeltaRename_isDeltaHom {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
    (D : DeltaStructure p A) {S T : Type u} (e : S ≃ T) :
    (relativeFreeDeltaStructure S D).IsDeltaHom (relativeFreeDeltaStructure T D)
      (MvPolynomial.renameEquiv A (Equiv.prodCongr e (Equiv.refl ℕ))).toRingEquiv.toRingHom := by
  apply DeltaStructure.isDeltaHom_mvPolynomial
  · intro a
    change MvPolynomial.rename (Equiv.prodCongr e (Equiv.refl ℕ))
      ((relativeFreeDeltaStructure S D).delta (MvPolynomial.C a)) =
        (relativeFreeDeltaStructure T D).delta
          (MvPolynomial.rename (Equiv.prodCongr e (Equiv.refl ℕ)) (MvPolynomial.C a))
    rw [relativeFreeDeltaStructure_delta_C, MvPolynomial.rename_C, MvPolynomial.rename_C,
      relativeFreeDeltaStructure_delta_C]
  · rintro ⟨s, i⟩
    change MvPolynomial.rename (Equiv.prodCongr e (Equiv.refl ℕ))
      ((relativeFreeDeltaStructure S D).delta (MvPolynomial.X (s, i))) =
        (relativeFreeDeltaStructure T D).delta
          (MvPolynomial.rename (Equiv.prodCongr e (Equiv.refl ℕ)) (MvPolynomial.X (s, i)))
    rw [relativeFreeDeltaStructure_delta_X, MvPolynomial.rename_X, MvPolynomial.rename_X]
    exact (relativeFreeDeltaStructure_delta_X T D (e s) i).symm

section Affine

variable (p : ℕ) [Fact p.Prime] (r n : ℕ)

local notation "Z" => (crystallineBasePrism p)
local notation "Idx" => (AffineIndex r n)
local notation "A₀" => (crystallineBase p)
local notation "B₀" => RelativeFreeDeltaRing (R := A₀) Idx
local notation "B" => completedFreeDelta Z Idx
local notation "D₀" => relativeFreeDeltaStructure Idx (OrientedPrism.deltaStructure Z)
local notation "D" => completedFreeDeltaStructure Z Idx
local notation "uB" => crystallineCompletedFreeDeltaUnit p Idx

/-- affine 模型の第 0 頂点との差。 -/
@[expose] def crystallineAffineDifference (t : ULift.{u} (Fin r × Fin n)) :
    completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r n) :=
  affineVariable Z r n t.down.1 t.down.2.succ - affineVariable Z r n t.down.1 0

private def rawDifference (t : ULift.{u} (Fin r × Fin n)) :
    RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n) :=
  MvPolynomial.X (⟨(t.down.1, t.down.2.succ)⟩, 0) -
    MvPolynomial.X (⟨(t.down.1, 0)⟩, 0)

private theorem unit_rawDifference (t : ULift.{u} (Fin r × Fin n)) :
    uB (rawDifference p r n t) = crystallineAffineDifference p r n t := by
  rw [rawDifference, map_sub]
  rfl

set_option maxHeartbeats 4000000 in
-- 添字の付け替えに沿う二つの剰余表示を照合する。
private theorem rawDivision_primeRegular :
    IsSMulRegular
      (DeltaAdjoinDivision D₀ (p : B₀) (rawDifference.{u} p r n))
      (p : DeltaAdjoinDivision D₀ (p : B₀) (rawDifference.{u} p r n)) := by
  let e := crystallineSplitEquiv.{u} r n
  let E := relativeFreeDeltaStructure (CrystallineSplitIndex.{u} r n) (Z).deltaStructure
  let R := RelativeFreeDeltaRing (R := crystallineBase.{u} p) (CrystallineSplitIndex.{u} r n)
  let ρ : R ≃+* B₀ := (MvPolynomial.renameEquiv A₀ (Equiv.prodCongr e (Equiv.refl ℕ))).toRingEquiv
  let b (t : ULift.{u} (Fin r × Fin n)) : ULift.{u} (Fin r) := ⟨t.down.1⟩
  let v : ULift.{u} (Fin r × Fin n) → R := crystallineFreeDivisionDifference b
  have hρ : E.IsDeltaHom D₀ ρ.toRingHom := freeDeltaRename_isDeltaHom (Z).deltaStructure e
  have hX (t : CrystallineSplitIndex.{u} r n) (i : ℕ) :
      ρ (MvPolynomial.X (t, i)) = MvPolynomial.X (e t, i) :=
    MvPolynomial.rename_X _ _
  have hv : (fun s => ρ (v s)) = rawDifference.{u} p r n := by
    funext t
    obtain ⟨⟨j, i⟩⟩ := t
    dsimp only [v, crystallineFreeDivisionDifference]
    rw [map_sub, hX, hX]
    rfl
  let e0 := crystallineFreeDivisionEquiv (Z).deltaStructure b
  have h₀ := regular_of_equiv e0.symm
    (crystallineRawFreeDelta_primeRegular p (CrystallineSplitIndex.{u} r n))
  exact baseChange_equiv_primeRegular E D₀ ρ hρ v (rawDifference.{u} p r n) hv h₀

/-- 完備自由 δ 環で差の p 除算を課しても p は正則。 -/
theorem crystallineAffineDivision_primeRegular :
    IsSMulRegular (DeltaAdjoinDivision D (p : B) (crystallineAffineDifference.{u} p r n))
      (p : DeltaAdjoinDivision D (p : B) (crystallineAffineDifference.{u} p r n)) := by
  let a := rawDifference.{u} p r n
  have hsq := deltaAdjoinDivisionBaseChange_isPushout D₀ D (uB)
    (crystallineCompletedFreeDeltaUnit_isDeltaHom p Idx) (p : B₀) a
  have h := crystallinePrimeRegular_of_isPushout p _ _ _ _ hsq
    (completedFreeDelta_unit_completelyFlat p (AffineIndex.{u} r n)) (rawDivision_primeRegular.{u} p r n)
  rw [map_natCast, show (fun s => (uB) (a s)) = crystallineAffineDifference p r n
    from funext (unit_rawDifference p r n)] at h
  exact h

/-- 完備自由 δ 環で差の Frobenius 像の p 除算を課しても p は正則。 -/
theorem crystallineAffineFrobeniusDivision_primeRegular :
    let y := fun t : ULift.{u} (Fin r × Fin n) =>
      (D).frobeniusLift (crystallineAffineDifference p r n t)
    IsSMulRegular (DeltaAdjoinDivision D (p : B) y)
      (p : DeltaAdjoinDivision D (p : B) y) := by
  exact baseChange_frobenius_primeRegular D (crystallineAffineDifference.{u} p r n)
    (crystallineCompletedFreeDelta_primeRegular p (AffineIndex.{u} r n))
    (crystallineCompletedFreeDeltaResidue p (AffineIndex.{u} r n))
    (crystallineAffineDivision_primeRegular.{u} p r n)

end Affine

end SerrePositivity.BhattScholze.Prismatic
