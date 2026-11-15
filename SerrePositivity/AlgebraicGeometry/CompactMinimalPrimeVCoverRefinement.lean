module

public import SerrePositivity.AlgebraicGeometry.FlatModelBaseChangeRefinement
public import SerrePositivity.AlgebraicGeometry.GenericFlatNoetherianModel
public import SerrePositivity.AlgebraicGeometry.FiniteTypeFlatteningNoetherian
public import SerrePositivity.AlgebraicGeometry.AffineTensorModelPullback
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAway
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper

/-!
概要：被約環で極小素点集合が準コンパクトなら、有限表示 v 被覆を fppf–proper で細分する。
方針：実際の Noether 係数模型を平坦化し、その平坦な閉部分を底変換して C02 を適用する。
規約：Rydh Proposition 3.7 の場合。元の射の平坦性・固有性は仮定しない。
使われ方：A07 で C01 の整拡大後に適用し、有限表示段への模型移送につなぐ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 被約環の極小素点集合が準コンパクトなら、有限表示の affine v 被覆は fppf–proper 細分を持つ。 -/
theorem exists_fppf_proper_refinement_vCover_affineReduced_compact_minimalPrimes
    (R B : Type u) [CommRing R] [IsReduced R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B]
    (hmin : IsCompact {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R})
    (hf : IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    ∃ (T W : Scheme.{u}) (q : W ⟶ T) (r : T ⟶ Spec (CommRingCat.of R))
      (b : W ⟶ Spec (CommRingCat.of B)),
      IsProper r ∧ LocallyOfFinitePresentation r ∧ Surjective r ∧ Flat q ∧
      LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ Surjective q ∧
      b ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = q ≫ r := by
  classical
  obtain ⟨A, _, _, _, C, _, _, hA, hN, hC, he, U, hUc, hflat, hURc, hURd, hMin⟩ :=
    exists_generic_flat_noetherian_model R B hmin
  letI : IsNoetherianRing A := hN
  letI : Algebra.FinitePresentation A C := hC
  obtain ⟨e⟩ := he
  let f₀ := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let g := Spec.map (CommRingCat.ofHom (algebraMap A R))
  letI : LocallyOfFinitePresentation f₀ :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr hC)
  obtain ⟨J, hJU, hJflat⟩ := exists_admissible_flat_strictTransformπ_of_finiteType f₀ U hflat
  let p₀ := blowupπ J
  let i₀ := strictTransformι f₀ U J
  letI : IsClosedImmersion i₀ := by dsimp only [i₀]; infer_instance
  letI : Flat (i₀ ≫ pullback.snd f₀ p₀) := hJflat
  letI : LocallyOfFiniteType (i₀ ≫ pullback.snd f₀ p₀) := by infer_instance
  letI : QuasiCompact (i₀ ≫ pullback.snd f₀ p₀) := by infer_instance
  letI : LocallyOfFinitePresentation (i₀ ≫ pullback.snd f₀ p₀) := by infer_instance
  have hP : ∀ s : Spec (CommRingCat.of A), s ∈ U → s ∈ Set.range p₀ := by
    letI : IsIso (p₀ ∣_ U) := by
      change IsIso (blowupπ J ∣_ U)
      rw [← hJU]
      exact blowupπ_restrict_complement_isIso J
    exact range_contains_open_of_isIso_restrict p₀ U
  have hI : ∀ z : (pullback f₀ p₀ : Scheme.{u}),
      pullback.snd f₀ p₀ z ∈ p₀ ⁻¹ᵁ U → z ∈ Set.range i₀ := by
    change ∀ z : strictTransformAmbient f₀ J,
      pullback.snd f₀ (blowupπ J) z ∈ blowupπ J ⁻¹ᵁ U →
      z ∈ Set.range (strictTransformι f₀ U J)
    intro z hz
    let V := strictTransformOpen f₀ U J
    have hzV : z ∈ V := by
      change z ∈ strictTransformOpen f₀ U J
      rw [strictTransformOpen_eq]
      exact hz
    have hsupport : z ∈ V.ι.ker.support := V.ι.range_subset_ker_support ⟨⟨z, hzV⟩, rfl⟩
    change z ∈ Set.range V.ι.ker.subschemeι
    exact (Set.ext_iff.mp V.ι.ker.range_subschemeι z).mpr hsupport
  exact exists_fppf_proper_refinement_of_flat_model (isPullback_affineTensorModel e) hf
    p₀ i₀ U hP hURc hURd hI

end SerrePositivity.AlgebraicGeometry
