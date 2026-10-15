module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionResidueFlat

/-! # raw除算包の残余商での次入力の正則性

既存の残余商の平坦性を使う。一般のraw環のp正則性は結論しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 適切な係数商で正則な元の像は、任意元族のraw(p,d)残余商でも正則。 -/
theorem deltaAdjoinDivisionResidue_isSMulRegular
    (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (w : Aˣ) (hw : (w : A) = D.delta d) (x : A)
    (hx : IsSMulRegular (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) d a) x)) :
    IsSMulRegular (DeltaAdjoinDivisionResidue D d a)
      (Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d a)
        (deltaAdjoinDivisionMap D d a x)) := by
  let L := RelativeFreeDeltaRing (R := A) σ
  have hpL : Function.Injective (fun t : L ↦ (p : L) * t) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L)
    have h' : IsSMulRegular L (p : L) := by simpa only [map_natCast] using h
    exact h'
  let := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a w hw
  let := deltaAdjoinDivisionResidue_moduleFlat D hpA hpL hg d a w hw
  have h := hx.of_flat (S := DeltaAdjoinDivisionResidue D d a)
  change IsSMulRegular (DeltaAdjoinDivisionResidue D d a)
    (deltaAdjoinDivisionResidueBaseMap D hpA hpL hg d a w hw (Ideal.Quotient.mk _ x)) at h
  rw [deltaAdjoinDivisionResidueBaseMap_mk] at h
  exact h

/-- d=pの場合、raw残余イデアルは実際のp主イデアルと一致する。 -/
theorem deltaAdjoinDivisionPResidueIdeal_eq (D : DeltaStructure p A) (a : σ → A) :
    deltaAdjoinDivisionResidueIdeal D (p : A) a =
      Ideal.span {(p : DeltaAdjoinDivision D (p : A) a)} := by
  rw [deltaAdjoinDivisionResidueIdeal, map_natCast]
  exact congrArg Ideal.span
    (Set.insert_eq_of_mem (Set.mem_singleton (p : DeltaAdjoinDivision D (p : A) a)))

/-- raw(p,p)残余商とraw包の実p商との、標準代表元を保つ比較。 -/
def deltaAdjoinDivisionPQuotientResidueEquiv (D : DeltaStructure p A) (a : σ → A) :
    (DeltaAdjoinDivision D (p : A) a ⧸
      Ideal.span {(p : DeltaAdjoinDivision D (p : A) a)}) ≃+*
        DeltaAdjoinDivisionResidue D (p : A) a :=
  Ideal.quotEquivOfEq (deltaAdjoinDivisionPResidueIdeal_eq D a).symm

/-- 比較はすべてのraw包の元の標準商像を保つ。 -/
theorem deltaAdjoinDivisionPQuotientResidueEquiv_mk
    (D : DeltaStructure p A) (a : σ → A) (z : DeltaAdjoinDivision D (p : A) a) :
    deltaAdjoinDivisionPQuotientResidueEquiv D a (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ z :=
  Ideal.quotEquivOfEq_mk _ _

/-- 適切な係数商で正則な次入力は、任意元族raw p除算包の実mod p商でも正則。 -/
theorem deltaAdjoinDivisionModP_next_isSMulRegular
    (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : σ → A) (w : Aˣ) (hw : (w : A) = D.delta (p : A)) (x : A)
    (hx : IsSMulRegular (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) a)
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A) a) x)) :
    IsSMulRegular (DeltaAdjoinDivision D (p : A) a ⧸
      Ideal.span {(p : DeltaAdjoinDivision D (p : A) a)})
      (Ideal.Quotient.mk (Ideal.span {(p : DeltaAdjoinDivision D (p : A) a)})
        (deltaAdjoinDivisionMap D (p : A) a x)) := by
  let e := deltaAdjoinDivisionPQuotientResidueEquiv D a
  have hr := deltaAdjoinDivisionResidue_isSMulRegular D hpA hg (p : A) a w hw x hx
  intro z t hzt
  apply e.injective
  apply hr
  change Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D (p : A) a x) * z =
    Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D (p : A) a x) * t at hzt
  have h := congrArg e hzt
  rw [map_mul, map_mul, deltaAdjoinDivisionPQuotientResidueEquiv_mk] at h
  exact h

end SerrePositivity.BhattScholze
