module

public import SerrePositivity.AlgebraicGeometry.InductiveCenterBaseChange

/-!
概要：帰納的レベルは任意の基底変更で保たれる。
方針：実際の細分を二段ずつ底変換し、中心上の比較の同型で帰納仮定を移す。
規約：底変換の平坦性と基底の Noether 性を要求しない。
使われ方：G3 の有限型模型からの帰納的レベルの移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
namespace ProperInductiveLevel

/-- BS17 Definition 2.5 の帰納的レベルは任意の底変換で保たれる。 -/
theorem baseChange {X Y T : Scheme.{u}} {n : ℕ} (f : X ⟶ Y) (g : T ⟶ Y)
    (hf : ProperInductiveLevel n f) : ProperInductiveLevel n (pullback.snd f g) := by
  induction n generalizing X Y T with
  | zero => exact zero_baseChange f g hf
  | succ n ih =>
    obtain ⟨X', X₀, Y₀, i, r, q, a, J, hi, his, hif, hr, hrs, hrf, hJ, hIso,
      hn, hq, hqf, hqs, hqfp, ha⟩ := hf
    letI := hi
    letI := his
    letI := hif
    letI := hr
    letI := hrs
    letI := hrf
    letI := hJ
    letI := hIso
    letI := hq
    letI := hqf
    letI := hqs
    letI := hqfp
    let Y₁ := pullback i g
    let h : Y₁ ⟶ Y₀ := pullback.fst i g
    let X₁ := pullback r h
    let X'₁ := pullback q (pullback.fst r h)
    let i₁ : Y₁ ⟶ T := pullback.snd i g
    let r₁ : X₁ ⟶ Y₁ := pullback.snd r h
    let q₁ : X'₁ ⟶ X₁ := pullback.snd q (pullback.fst r h)
    let J₁ := J.comap h
    let z := inductiveCenterBaseChangeProjection J h
    have HJ := isPullback_inductiveCenterBaseChangeProjection J h
    have hJ₁ : LocallyOfFinitePresentation J₁.subschemeι :=
      MorphismProperty.of_isPullback HJ.flip inferInstance
    have Hcenter := isPullback_inductiveCenterRestrictionBaseChangeMap r h J
    have hn₁ : ProperInductiveLevel n (pullback.snd r₁ J₁.subschemeι) := by
      have hn' := ih (pullback.snd r J.subschemeι) z hn
      have H := (iso_source_iff Hcenter.isoPullback
        (pullback.snd (pullback.snd r J.subschemeι) z) n).mpr hn'
      simpa only [z, IsPullback.isoPullback_hom_snd] using H
    have hpre : r₁ ⁻¹ᵁ h ⁻¹ᵁ centerComplement J =
        pullback.fst r h ⁻¹ᵁ r ⁻¹ᵁ centerComplement J := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
    have Hres := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback r h)
      (US := centerComplement J) (UT := h ⁻¹ᵁ centerComplement J)
      (UX := r ⁻¹ᵁ centerComplement J) (UY := r₁ ⁻¹ᵁ h ⁻¹ᵁ centerComplement J)
      le_rfl le_rfl (by rw [hpre]; simp)
    have hrRes : IsIso (r.resLE (centerComplement J) (r ⁻¹ᵁ centerComplement J) le_rfl) := by
      rwa [Scheme.Hom.resLE_eq_morphismRestrict]
    have hIso₁ : IsIso (r₁ ∣_ centerComplement J₁) := by
      have H := Hres.isIso_snd_of_isIso hrRes
      change IsIso (pullback.snd r h ∣_ centerComplement (J.comap h))
      rw [← preimage_centerComplement_comap J h]
      simpa only [r₁, Scheme.Hom.resLE_eq_morphismRestrict] using H
    have hw : (pullback.fst q (pullback.fst r h) ≫ a) ≫ f =
        (q₁ ≫ r₁ ≫ i₁) ≫ g := by
      calc
        (pullback.fst q (pullback.fst r h) ≫ a) ≫ f =
            (pullback.fst q (pullback.fst r h) ≫ q) ≫ r ≫ i := by
          simp only [Category.assoc, ha]
        _ = (q₁ ≫ pullback.fst r h) ≫ r ≫ i := by rw [pullback.condition]
        _ = q₁ ≫ (pullback.fst r h ≫ r) ≫ i := by simp only [Category.assoc]
        _ = q₁ ≫ (r₁ ≫ h) ≫ i := by rw [pullback.condition]
        _ = (q₁ ≫ r₁) ≫ (h ≫ i) := by simp only [Category.assoc]
        _ = (q₁ ≫ r₁) ≫ (i₁ ≫ g) := by rw [pullback.condition]
        _ = (q₁ ≫ r₁ ≫ i₁) ≫ g := by simp only [Category.assoc]
    let a₁ : X'₁ ⟶ pullback f g :=
      pullback.lift (pullback.fst q (pullback.fst r h) ≫ a) (q₁ ≫ r₁ ≫ i₁) hw
    exact ⟨X'₁, X₁, Y₁, i₁, r₁, q₁, a₁, J₁, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, hJ₁, hIso₁, hn₁,
      inferInstance, inferInstance, inferInstance, inferInstance, by simp [a₁]⟩

end ProperInductiveLevel
end SerrePositivity.AlgebraicGeometry
