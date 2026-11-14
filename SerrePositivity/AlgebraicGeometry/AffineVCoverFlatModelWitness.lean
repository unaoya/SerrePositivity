module

public import SerrePositivity.AlgebraicGeometry.IntegralClosedFlatModelWitness
public import SerrePositivity.AlgebraicGeometry.IntegralClosedFlatRefinement
public import SerrePositivity.AlgebraicGeometry.CompactMinimalPrimeIntegralCover
public import SerrePositivity.AlgebraicGeometry.CompactMinimalPrimeClosedRefinementModel

/-!
概要：任意の affine 基底の有限表示な affine v 被覆を fppf–proper で細分する。
方針：被約化と C01 の整全射の後に実際の Noether 平坦閉部分模型を選び、有限表示段へ戻す。
規約：基底の被約性・Noether 性、元の射の平坦性・固有性は仮定しない。
使われ方：A07 の一般の始域の有限アフィン被覆に適用する出口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u

/-- 任意の環上の有限表示な affine v 被覆に、固定の有限型 ℤ 上の平坦模型の証人を添えられる。 -/
theorem exists_flat_model_refinement_witness_vCover_affineRing
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (hf : IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap R C)))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra ℤ A),
      Algebra.FiniteType ℤ A ∧ IsNoetherianRing A ∧
      ∃ (Y Z : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of A)) (q : Z ⟶ Y),
        IsProper p ∧ LocallyOfFinitePresentation p ∧ Flat q ∧
        LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q ∧
        ∃ (T : Scheme.{u}) (r : T ⟶ Spec (CommRingCat.of R)) (β : T ⟶ Y),
          IsProper r ∧ LocallyOfFinitePresentation r ∧ Surjective r ∧
          Surjective (pullback.snd q β) ∧
          ∃ l : pullback q β ⟶ Spec (CommRingCat.of C),
            l ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) = pullback.snd q β ≫ r := by
  classical
  obtain ⟨B, e, hB, he, hes, hmin⟩ :=
    exists_integral_surjective_reduced_compact_minimalPrimes (CommRingCat.of R)
  letI : Algebra R B := e.toAlgebra
  letI : IsReduced B := hB
  letI : Algebra.IsIntegral R B := (algebraMap_isIntegral_iff).mp he
  letI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B))) := hes
  let S := B ⊗[R] C
  letI : Algebra.FinitePresentation B S :=
    ((Algebra.Presentation.ofFinitePresentation R C).baseChange B).finitePresentation_of_isFinite
  let f := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let s := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let x := Spec.map (CommRingCat.ofHom (algebraMap B S))
  let eTensor : B ⊗[R] C ≃ₐ[B] S := AlgEquiv.refl
  let a := Spec.map (CommRingCat.ofHom (eTensor.toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[R] S).toRingHom))
  have hTensor : IsPullback a x f s :=
    isPullback_affineTensorModel (A := R) (R := B) (S := C) eTensor
  have hfS : IsSchemeVCover x := IsSchemeVCover.baseChange hTensor hf
  obtain ⟨A, _, _, _, hA, hN, C₀, _, _, hC₀, Y, Z, p, i₀, hp, hpfp, hi₀,
      hq, hqfp, hqqc, K, hK, hr, hqs, lS, hlS⟩ :=
    exists_noether_flat_closed_refinement_model_compact_minimalPrimes B S hmin hfS
  letI : Algebra.FiniteType ℤ A := hA
  letI : IsProper p := hp
  letI : LocallyOfFinitePresentation p := hpfp
  letI : IsClosedImmersion i₀ := hi₀
  let q₀ := i₀ ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A C₀))) p
  letI : Flat q₀ := hq
  letI : LocallyOfFinitePresentation q₀ := hqfp
  letI : QuasiCompact q₀ := hqqc
  haveI : IsAffineHom (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A C₀))) p) :=
    MorphismProperty.pullback_snd _ p inferInstance
  letI : IsAffineHom q₀ := MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  let v := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  let b := K.subschemeι ≫ v
  let E := pullbackLeftPullbackSndIso q₀ v K.subschemeι
  letI : Surjective (K.subschemeι ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A B)))) := hr
  letI : Surjective (pullback.snd q₀ b) := by
    constructor
    intro z
    obtain ⟨w, hw⟩ := hqs.surj z
    refine ⟨E.hom w, ?_⟩
    change (E.hom ≫ pullback.snd q₀ b) w = z
    rw [pullbackLeftPullbackSndIso_hom_snd]
    exact hw
  let lInf := E.inv ≫ lS ≫ a
  letI : LocallyOfFinitePresentation f :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hlInf : lInf ≫ f = pullback.snd q₀ b ≫ K.subschemeι ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ s := by
    dsimp only [lInf]
    rw [Category.assoc, Category.assoc, hTensor.w]
    rw [← Category.assoc lS x s, hlS]
    change E.inv ≫ pullback.snd (pullback.snd q₀ v) K.subschemeι ≫ K.subschemeι ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ s =
      pullback.snd q₀ (K.subschemeι ≫ v) ≫ K.subschemeι ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ s
    rw [pullbackLeftPullbackSndIso_inv_snd_snd_assoc]
  obtain ⟨T, r, β, hr, hrfp, hrs, hqs, l, hlf⟩ :=
    exists_proper_flat_model_witness_of_integral_closed_model R B A (algebraMap A B)
      p q₀ K hK f lInf hlInf
  exact ⟨A, inferInstance, inferInstance, hA, hN, Y, Z, p, q₀,
    hp, hpfp, hq, hqfp, hqqc, inferInstance, T, r, β, hr, hrfp, hrs, hqs, l, hlf⟩

end SerrePositivity.AlgebraicGeometry
