module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineAffineDivision
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallineDivisionEnvelope
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallineDivisionEnvelope

/-!
# 結晶基底の affine envelope の p 除算表示

## 概要
Čech–Alexander 模型の各項を、差の完備 p 除算環で表す。

## 方針
差で生成されるイデアルを照合し、envelope の普遍性で比較する。

## 規約
第 0 頂点との差の添字には第 0 頂点自身を含めない。

## 使われ方
結晶の橋の mod p 押し出し比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

private abbrev base (p : ℕ) [Fact p.Prime] : OrientedPrism p (crystallineBase.{u} p) := crystallineBasePrism p

local notation "Z" => (base p)
local notation "B" n => completedFreeDelta Z (AffineIndex r (SimplexCategory.len n))
local notation "D" n => completedFreeDeltaStructure Z (AffineIndex r (SimplexCategory.len n))
local notation "β" n => completedFreeDeltaBase Z (AffineIndex r (SimplexCategory.len n))

private abbrev affineTerm (n : SimplexCategory) :=
  affineEnvelopeTerm Z (crystallineBaseBounded p) r n.len (polyCutoff Z r) le_rfl

private theorem affineDifferenceIdeal_eq (n : SimplexCategory) :
    affineDifferenceIdeal Z r n.len = crystallineDivisionIdeal Z (β n) (crystallineAffineDifference.{u} p r n.len) := by
  change Ideal.span (insert ((β n) (Z).generator) (Set.range (fun ji : Fin r × Fin (n.len + 1) =>
      affineVariable Z r n.len ji.1 ji.2 - affineVariable Z r n.len ji.1 0))) =
    Ideal.span (insert ((β n) (Z).generator) (Set.range (crystallineAffineDifference.{u} p r n.len)))
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (hx | ⟨⟨j,i⟩,rfl⟩)
    · exact Ideal.subset_span (Or.inl hx)
    · refine Fin.cases ?_ (fun t => ?_) i
      · change affineVariable Z r n.len j 0 - affineVariable Z r n.len j 0 ∈ _
        rw [sub_self]
        exact Ideal.zero_mem _
      · exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨⟨(j,t)⟩, rfl⟩)
  · rw [Ideal.span_le]
    rintro x (hx | ⟨⟨⟨j,i⟩⟩,rfl⟩)
    · exact Ideal.subset_span (Or.inl hx)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨(j,i.succ),rfl⟩)

private theorem envelope_of_eq_ideal {p : ℕ} [Fact p.Prime]
    {A R C : Type u} [CommRing A] [CommRing R] [CommRing C]
    (P : OrientedPrism p A) (DS : DeltaStructure p R) (i : A →+* R)
    (hi : P.deltaStructure.IsDeltaHom DS i) (Q : OrientedPrism p C) (η : R →+* C)
    {I J : Ideal R} (e : I = J) (hI : i P.generator ∈ I) (hJ : i P.generator ∈ J)
    (h : IsPrismaticEnvelope P DS i hi J hJ Q η) : IsPrismaticEnvelope P DS i hi I hI Q η := by
  subst J
  exact h

private theorem affineEnvelope_existsEquiv (n : SimplexCategory) :
    ∃ e : (affineTerm.{u} p r n).X.B ≃+*
        ClassicalDeltaDivisionCompletion (D n) (p : B n) (crystallineAffineDifference.{u} p r n.len),
      (affineTerm.{u} p r n).X.Q.deltaStructure.IsDeltaHom
        (classicalDeltaDivisionStructure (D n) (p : B n) (crystallineAffineDifference.{u} p r n.len)) e.toRingHom ∧
      e.toRingHom.comp (affineTerm.{u} p r n).η =
        classicalDeltaDivisionMap (D n) (p : B n) (crystallineAffineDifference.{u} p r n.len) := by
  let a := crystallineAffineDifference.{u} p r n.len
  let P := crystallineDivisionPrism (D n) a
  have h := crystallineDivision_isPrismaticEnvelope Z (crystallineBase_generator p)
    (D n) (β n) (completedFreeDeltaBase_isDeltaHom Z (AffineIndex r n.len)) a
  have h' : IsPrismaticEnvelope Z (D n) (β n) (completedFreeDeltaBase_isDeltaHom Z _)
      (affineDifferenceIdeal Z r n.len) (by
        unfold affineDifferenceIdeal
        exact Ideal.subset_span (Set.mem_insert _ _))
      P (classicalDeltaDivisionMap (D n) (p : B n) a) := by
    exact envelope_of_eq_ideal Z (D n) (β n) (completedFreeDeltaBase_isDeltaHom Z _) P _
      (affineDifferenceIdeal_eq p r n) _ _ h
  obtain ⟨e, he, hc⟩ := (affineTerm.{u} p r n).envelope.unique Z h'
  rw [crystallineDivisionPrism_deltaStructure] at he
  exact ⟨e, he, hc⟩

end SerrePositivity.BhattScholze.Prismatic
