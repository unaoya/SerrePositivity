module

public import SerrePositivity.AlgebraicGeometry.CompactGenericFlatnessAffine

/-!
概要：一般点集合が準コンパクトな被約アフィン基底への有限表示射の一般平坦性。
方針：アフィン版を始域の有限アフィン開被覆に適用し、基底の開を共通に狭める。
規約：元の基底の Noether 性を仮定しない。準コンパクト性は始域に要求する。
使われ方：Rydh 3.7 の Noether 模型への降下前の、準コンパクト稠密な平坦開。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

set_option backward.isDefEq.respectTransparency false in
private theorem exists_compact_generic_flat_of_isAffine
    {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}} [IsReduced R]
    (f : X ⟶ Spec R) [LocallyOfFinitePresentation f]
    (hmin : IsCompact {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R}) :
    ∃ U : (Spec R).Opens, IsCompact U.carrier ∧ Dense U.carrier ∧
      (∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R → q ∈ U) ∧ Flat (f ∣_ U) := by
  let g := X.isoSpec.inv ≫ f
  let φ := Spec.preimage g
  have hg : Spec.map φ = g := Spec.map_preimage g
  let : Algebra R Γ(X, ⊤) := φ.hom.toAlgebra
  have hφ : φ.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
      (hg ▸ (inferInstance : LocallyOfFinitePresentation g))
  let : Algebra.FinitePresentation R Γ(X, ⊤) := hφ
  obtain ⟨U, hUc, hUd, hMU, hflat⟩ :=
    exists_compact_dense_open_flat_restrict_specMap_of_finitePresentation R Γ(X, ⊤) hmin
  change Flat (Spec.map φ ∣_ U) at hflat
  rw [hg, morphismRestrict_comp] at hflat
  exact ⟨U, hUc, hUd, hMU, (MorphismProperty.cancel_left_of_respectsIso @Flat
    (X.isoSpec.inv ∣_ f ⁻¹ᵁ U) (f ∣_ U)).mp hflat⟩

set_option backward.isDefEq.respectTransparency false in
/-- 一般点集合が準コンパクトな被約アフィン基底への局所有限表示射は、
始域が準コンパクトなら、全一般点を含む準コンパクト稠密開上で平坦。 -/
theorem exists_compact_dense_open_flat_restrict_of_compact_generics
    {X : Scheme.{u}} [CompactSpace X] {R : CommRingCat.{u}} [IsReduced R]
    (f : X ⟶ Spec R) [LocallyOfFinitePresentation f]
    (hmin : IsCompact {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R}) :
    ∃ U : (Spec R).Opens, IsCompact U.carrier ∧ Dense U.carrier ∧
      (∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R → q ∈ U) ∧ Flat (f ∣_ U) := by
  let 𝒰 := X.affineCover.finiteSubcover
  have h (i : 𝒰.I₀) : ∃ U : (Spec R).Opens, IsCompact U.carrier ∧
      Dense U.carrier ∧ (∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R → q ∈ U) ∧
      Flat ((𝒰.f i ≫ f) ∣_ U) := by
    have : IsAffine (𝒰.X i) := by
      rw [X.affineCover.finiteSubcover_X]
      exact Scheme.isAffine_affineCover X _
    exact exists_compact_generic_flat_of_isAffine (𝒰.f i ≫ f) hmin
  choose V hVc hVd hMV hflat using h
  let T := ⨅ i, V i
  have hMT (q : PrimeSpectrum R) (hq : q.asIdeal ∈ minimalPrimes R) : q ∈ T := by
    have hx : (q : Spec R) ∈ ⋂ i, (V i).carrier :=
      Set.mem_iInter.mpr fun i ↦ hMV i q hq
    have heq : T.carrier = ⋂ i, (V i).carrier := TopologicalSpace.Opens.coe_iInf V
    have hmem : (q : Spec R) ∈ T.carrier := heq.symm ▸ hx
    exact hmem
  obtain ⟨U, hUc, hUd, hUT, hMU⟩ :=
    exists_compact_denseOpen_of_contains_minimalPrimes R hmin T hMT
  refine ⟨U, hUc, hUd, hMU, ?_⟩
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat) (𝒰.restrict (f ⁻¹ᵁ U))
  intro i
  rw [Scheme.OpenCover.restrict_f, ← morphismRestrict_comp]
  let g := 𝒰.f i ≫ f
  let W := (V i).ι ⁻¹ᵁ U
  have hW : (V i).ι ''ᵁ W = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (hUT.trans (iInf_le V i))]
  rw [← MorphismProperty.arrow_mk_iso_iff @Flat
    (morphismRestrictRestrict g (V i) W ≪≫ morphismRestrictEq g hW)]
  let : Flat (g ∣_ V i) := hflat i
  exact inferInstance

end SerrePositivity.AlgebraicGeometry
