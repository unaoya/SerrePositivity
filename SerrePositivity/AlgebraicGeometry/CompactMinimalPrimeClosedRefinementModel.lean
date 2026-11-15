module

public import SerrePositivity.AlgebraicGeometry.FlatModelClosedRefinementWitness
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
/-- 有限表示 v 被覆の Noether 平坦模型と、底変換上の有限型閉包絡の実際の証人を保持する。 -/
theorem exists_noether_flat_closed_refinement_model_compact_minimalPrimes
    (R B : Type u) [CommRing R] [IsReduced R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B]
    (hmin : IsCompact {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R})
    (hf : IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra ℤ A) (_ : Algebra A R),
      Algebra.FiniteType ℤ A ∧ IsNoetherianRing A ∧
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
        Algebra.FinitePresentation A C ∧
        ∃ (Y₀ Z₀ : Scheme.{u}) (p₀ : Y₀ ⟶ Spec (CommRingCat.of A))
          (i₀ : Z₀ ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A C))) p₀),
          IsProper p₀ ∧ LocallyOfFinitePresentation p₀ ∧ IsClosedImmersion i₀ ∧
          Flat (i₀ ≫ pullback.snd _ _) ∧
          LocallyOfFinitePresentation (i₀ ≫ pullback.snd _ _) ∧
          QuasiCompact (i₀ ≫ pullback.snd _ _) ∧
          ∃ J : (pullback p₀ (Spec.map (CommRingCat.ofHom (algebraMap A R)))).IdealSheafData,
            IsFiniteTypeIdealSheaf J ∧
            Surjective (J.subschemeι ≫ pullback.snd _ _) ∧
            Surjective (pullback.snd
              (pullback.snd (i₀ ≫ pullback.snd _ _)
                (pullback.fst p₀ (Spec.map (CommRingCat.ofHom (algebraMap A R)))))
              J.subschemeι) ∧
            ∃ b : pullback
                (pullback.snd (i₀ ≫ pullback.snd _ _)
                  (pullback.fst p₀ (Spec.map (CommRingCat.ofHom (algebraMap A R)))))
                J.subschemeι ⟶ Spec (CommRingCat.of B),
              b ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
                pullback.snd _ _ ≫ J.subschemeι ≫ pullback.snd _ _ := by
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
  obtain ⟨L, hL, hr, hq, b, hb⟩ :=
    exists_flat_model_closed_refinement_witness (isPullback_affineTensorModel e) hf
      p₀ i₀ U hP hURc hURd hI
  exact ⟨A, inferInstance, inferInstance, inferInstance, hA, hN,
    C, inferInstance, inferInstance, hC, _, _, p₀, i₀, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, L, hL, hr, hq, b, hb⟩

end SerrePositivity.AlgebraicGeometry
