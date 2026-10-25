module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionLocalization

/-! # rawδ除算包の像のδ安定部分環としての最小性

相対自由δ環の反復δ座標と商の帰納法による。p正則性は不要。
分冪包候補への適用には、その候補のδ安定性を別途証明する必要がある。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 基底と初期変数の像を含むδ安定部分環は、raw包のδ射の全像を含む。 -/
theorem deltaAdjoinDivision_range_le_of_delta_stable {T : Type w} [CommRing T]
    (D : DeltaStructure p A) (E : DeltaStructure p T) (d : A) (a : σ → A)
    (f : DeltaAdjoinDivision D d a →+* T)
    (hf : (deltaAdjoinDivisionStructure D d a).IsDeltaHom E f) (S : Subring T)
    (hbase : ∀ r : A, f (deltaAdjoinDivisionMap D d a r) ∈ S)
    (hvar : ∀ s : σ, f (deltaAdjoinDivisionVariable D d a s) ∈ S)
    (hδ : ∀ t ∈ S, E.delta t ∈ S) : f.range ≤ S := by
  let F := relativeFreeDeltaStructure σ D
  let I := F.deltaClosure (deltaDivisionRelationIdeal d a)
  let q := Ideal.Quotient.mk I
  let g := f.comp q
  have hg : F.IsDeltaHom E g := hf.comp (F.isDeltaHom_quotient_mk I (F.isStable_deltaClosure _))
  have hX (s : σ) (n : ℕ) : g (MvPolynomial.X (s, n)) ∈ S := by
    rw [relativeFreeDeltaHom_X_iterates D E g hg s n]
    change E.delta^[n] (f (deltaAdjoinDivisionVariable D d a s)) ∈ S
    induction n with
    | zero => exact hvar s
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hδ _ ih
  rintro t ⟨b, rfl⟩
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  change g P ∈ S
  induction P using MvPolynomial.induction_on with
  | C r => exact hbase r
  | add P Q hP hQ => rw [map_add]; exact S.add_mem hP hQ
  | mul_X P z hP => rw [map_mul]; exact S.mul_mem hP (hX z.1 z.2)

/-- Aとy_s^p/pを含むδ安定部分環は、具体的A{φ(y_s)/p}の局所化内の像を含む。 -/
theorem deltaPDivisionToAway_range_le_of_delta_stable (D : DeltaStructure p A)
    (y : σ → A) (S : Subring (Localization.Away (p : A)))
    (hbase : ∀ r : A, algebraMap A (Localization.Away (p : A)) r ∈ S)
    (hpow : ∀ s : σ, IsLocalization.Away.invSelf (p : A) *
      (algebraMap A (Localization.Away (p : A)) (y s)) ^ p ∈ S)
    (hδ : ∀ t ∈ S, (deltaPDivisionAwayStructure D).delta t ∈ S) :
    (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range ≤ S := by
  let a := fun s ↦ D.frobeniusLift (y s)
  let f := deltaPDivisionToAway D a
  apply deltaAdjoinDivision_range_le_of_delta_stable D (deltaPDivisionAwayStructure D)
    (p : A) a f (deltaPDivisionToAway_spec D a).1 S ?_ ?_ hδ
  · intro r
    have hb := RingHom.congr_fun (deltaPDivisionToAway_spec D a).2.1 r
    exact hb ▸ hbase r
  · intro s
    have he : f (deltaAdjoinDivisionVariable D (p : A) a s) =
        IsLocalization.Away.invSelf (p : A) *
          (algebraMap A (Localization.Away (p : A)) (y s)) ^ p +
          algebraMap A (Localization.Away (p : A)) (D.delta (y s)) := by
      rw [(deltaPDivisionToAway_spec D a).2.2]
      change _ * algebraMap A _ (D.frobeniusLift (y s)) = _
      have hi : IsLocalization.Away.invSelf (p : A) *
          algebraMap A (Localization.Away (p : A)) (p : A) = 1 := by
        rw [mul_comm, IsLocalization.Away.mul_invSelf]
      rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, mul_add,
        ← mul_assoc, hi, one_mul]
    rw [he]
    exact S.add_mem (hpow s) (hbase _)

end SerrePositivity.BhattScholze
