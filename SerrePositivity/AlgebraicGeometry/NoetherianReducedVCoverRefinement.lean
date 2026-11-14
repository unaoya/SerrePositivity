module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeFlatteningAffineBase
public import SerrePositivity.AlgebraicGeometry.ValuativeFppfBlowupRefinement

/-!
概要：被約 Noether アフィン基底上の有限型 v 被覆を、fppf 射と blowup で細分する。
方針：一般平坦開に含まれる正則主開を取り、許容中心の平坦化と v 判定の全射性を使う。
規約：元の射に固有性を要求しない。非 Noether の場合の模型は後で供給する。
使われ方：Rydh 3.10 の被約 Noether アフィン段。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u

/-- 被約 Noether アフィン基底上の有限型 v 被覆の fppf–blowup 細分。 -/
theorem exists_fppf_blowup_refinement_vCover_affineNoetherianReduced
    {R : CommRingCat.{u}} [IsNoetherianRing R] [IsReduced R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [LocallyOfFiniteType f] [QuasiCompact f] (hf : IsSchemeVCover f) :
    ∃ (a : R) (_ : IsRegular a) (J : (Spec R).IdealSheafData),
      IsUAdmissibleCenter (PrimeSpectrum.basicOpen a) J ∧
      IsProper (blowupπ J) ∧ Surjective (blowupπ J) ∧
      IsIso (blowupπ J ∣_ PrimeSpectrum.basicOpen a) ∧
      ∃ (X' : Scheme.{u}) (g : X' ⟶ blowup J) (k : X' ⟶ X),
        Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧
          k ≫ f = g ≫ blowupπ J := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨U, hU, hflat⟩ := exists_dense_open_flat_restrict_of_compactSpace f
  obtain ⟨a, ha, hle⟩ := exists_nonZeroDivisor_basicOpen_le_of_dense R U hU
  let D : (Spec R).Opens := PrimeSpectrum.basicOpen a
  let V := U.ι ⁻¹ᵁ D
  have hV : U.ι ''ᵁ V = D := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hle]
  have hD : Flat (f ∣_ D) := (MorphismProperty.arrow_mk_iso_iff @Flat
    (morphismRestrictRestrict f U V ≪≫ morphismRestrictEq f hV)).mp
      (IsZariskiLocalAtTarget.restrict (P := @Flat) hflat V)
  have ha' := isRegular_iff_mem_nonZeroDivisors.mpr ha
  obtain ⟨J, hJ, hJflat⟩ := exists_admissible_flat_strictTransformπ_finiteType_affineBase f a ha' hD
  let : Flat (strictTransformπ f D J) := hJflat
  have hd : Dense D.carrier := by
    change Dense (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R))
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (IsLocalization.injective (Localization.Away a) (Submonoid.powers_le.mpr ha))]
    exact bot_le
  exact ⟨a, ha', J, hJ, exists_fppf_blowup_refinement_of_flat_strictTransform_vCover f hf D J hd hJ⟩


end SerrePositivity.AlgebraicGeometry
