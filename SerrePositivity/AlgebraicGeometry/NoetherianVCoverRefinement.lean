module

public import SerrePositivity.AlgebraicGeometry.NoetherianReducedVCoverRefinement
public import SerrePositivity.AlgebraicGeometry.AffineVCoverNilImmersion
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverSurjective
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
概要：Noether アフィン基底上の有限型 v 被覆の fppf–proper 細分。
方針：nilradical で被約化し、被約基底上の blowup 細分を元の基底へ合成する。
規約：基底の被約性・元の射の固有性を要求しない。
使われ方：Rydh 3.10 の Noether アフィンな段。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

/-- Noether アフィン基底上の有限型 v 被覆には fppf–proper 細分がある。 -/
theorem exists_fppf_proper_refinement_vCover_affineNoetherian
    {R : CommRingCat.{u}} [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : IsSchemeVCover f) :
    ∃ (T X' : Scheme.{u}) (q : T ⟶ Spec R) (g : X' ⟶ T) (k : X' ⟶ X),
      IsProper q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧ QuasiCompact q ∧
      Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧
      k ≫ f = g ≫ q := by
  let A := R ⧸ nilradical R
  letI : IsReduced A := by
    apply (RingHom.ker_isRadical_iff_reduced_of_surjective
      (f := Ideal.Quotient.mk (nilradical R)) Ideal.Quotient.mk_surjective).mp
    rw [Ideal.mk_ker]
    exact Ideal.radical_isRadical 0
  let r := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R)))
  let f₀ := pullback.snd f r
  have hf₀ : IsSchemeVCover f₀ :=
    IsSchemeVCover.baseChange (IsPullback.of_hasPullback f r) hf
  obtain ⟨a, ha, J, hJ, hproper, hsurj, _, X', g, k, hflat, hgsurj, hgfp, hgqc, hcomm⟩ :=
    exists_fppf_blowup_refinement_vCover_affineNoetherianReduced (R := CommRingCat.of A) f₀ hf₀
  letI : IsProper (blowupπ J) := hproper
  letI : Surjective (blowupπ J) := hsurj
  have hr : IsSchemeVCover r := (isSchemeVCover_specMap_iff _).mpr
    (isAffineVCover_quotient_of_le_nilradical (nilradical R) le_rfl)
  letI : Surjective r := hr.surjective
  refine ⟨blowup J, X', blowupπ J ≫ r, g, k ≫ pullback.fst f r,
    inferInstance, inferInstance, inferInstance, inferInstance,
    hflat, hgsurj, hgfp, hgqc, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hcomm, Category.assoc]

end SerrePositivity.AlgebraicGeometry
