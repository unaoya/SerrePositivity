module

public import SerrePositivity.AlgebraicGeometry.GenericFreeReducedAlgebra
public import SerrePositivity.CommutativeAlgebra.Localization.Away
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Baire.Lemmas

/-!
概要：被約局所 Noether 基底上の有限型射は、基底の稠密開上で平坦。
方針：任意の非空な基本開を係数環の局所化とみなし、そこで有限型代数の一般自由性を適用する。
規約：一つの自由な主開だけでなく、自由な主開すべての和が稠密であることを使う。
使われ方：BS17 Lemma 2.6 の平坦化の前に、稠密な平坦開を選ぶ。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

private theorem nontrivial_away_of_not_isNilpotent {R : Type u} [CommRing R]
    {r : R} (hr : ¬ IsNilpotent r) : Nontrivial (Localization.Away r) :=
  (IsLocalization.toLocalizationMap (.powers r) (Localization.Away r)).nontrivial hr

private theorem exists_free_basicOpen_subset
    (R B : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (r : R) (hr : ¬ IsNilpotent r) :
    ∃ s : R, PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r ∧
      (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum R)).Nonempty ∧
      Module.Free (Localization.Away s) (Localization.Away s ⊗[R] B) := by
  let C := Localization.Away r
  let : Nontrivial C := nontrivial_away_of_not_isNilpotent hr
  obtain ⟨g, hg, hfree⟩ := exists_nonzero_free_localization_of_finiteType_of_isReduced C
    (C ⊗[R] B)
  let a := (IsLocalization.Away.sec r g).1
  let L := Localization.Away g
  let D := Localization.Away (r * a)
  let : IsLocalization.Away (r * a) L := IsLocalization.Away.mul_of_associated r a g
    (IsLocalization.Away.associated_sec_fst r g)
  let e : L ≃ₐ[R] D := IsLocalization.algEquiv (.powers (r * a)) L D
  let : Nontrivial L :=
    nontrivial_away_of_not_isNilpotent (fun h => hg (isNilpotent_iff_eq_zero.mp h))
  let : Nontrivial D := e.toEquiv.symm.nontrivial
  obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum D))
  refine ⟨r * a, PrimeSpectrum.basicOpen_mul_le_left r a, ⟨q.comap (algebraMap R D), ?_⟩, ?_⟩
  · rw [← PrimeSpectrum.localization_away_comap_range D (r * a)]
    exact ⟨q, rfl⟩
  · let : Module.Free L (L ⊗[C] (C ⊗[R] B)) := hfree
    let : Module.Free L (L ⊗[R] B) := Module.Free.of_equiv
      (Algebra.TensorProduct.cancelBaseChange R C L L B).toLinearEquiv
    let := RingHomInvPair.of_ringEquiv e.toRingEquiv
    let := RingHomInvPair.of_ringEquiv_symm e.toRingEquiv
    exact Module.Free.of_equiv (tensorBaseChangeSemilinearEquiv e)

set_option backward.isDefEq.respectTransparency false in
private theorem flat_restrict_basicOpen_of_free
    {R B : CommRingCat.{u}} [Algebra R B] (r : R)
    [Module.Free (Localization.Away r) (Localization.Away r ⊗[R] B)] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ PrimeSpectrum.basicOpen r) := by
  rw [MorphismProperty.arrow_mk_iso_iff @Flat
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap R B)) r), Flat.SpecMap_iff]
  change (Localization.awayMap (algebraMap R B) r).Flat
  let := SerrePositivity.GenericEtale.awayAlgebra R B r
  change Module.Flat (Localization.Away r) (Localization.Away (algebraMap R B r))
  exact Module.Flat.of_linearEquiv
    (SerrePositivity.originalAwayTensorEquiv R B r).symm.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
private theorem flat_restrict_iSup {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} (V : ι → Y.Opens) (h : ∀ i, Flat (f ∣_ V i)) :
    Flat (f ∣_ ⨆ i, V i) := by
  let U := ⨆ i, V i
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @Flat)
  intro x
  have hx : x.val ∈ (⨆ i, V i : Y.Opens) := x.property
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let W := U.ι ⁻¹ᵁ V i
  refine ⟨W, hi, ?_⟩
  have hW : U.ι ''ᵁ W = V i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (le_iSup V i)]
  rw [MorphismProperty.arrow_mk_iso_iff @Flat
    (morphismRestrictRestrict f U W ≪≫ morphismRestrictEq f hW)]
  exact h i

set_option backward.isDefEq.respectTransparency false in
/--
概要：被約 Noether アフィン基底上の有限型アフィン射は、基底のある稠密開上で平坦。
方針：自由になる基本開の和を取り、任意の非空基本開で一般自由性を適用して稠密性を示す。
規約：自由階数の有限性や、基底の既約性は仮定しない。
使われ方：BS17 Lemma 2.6 に向けた固有射の平坦化の開始点。
-/
theorem exists_dense_open_flat_restrict_specMap_of_finiteType
    (R B : CommRingCat.{u}) [IsNoetherianRing R] [IsReduced R]
    [Algebra R B] [Algebra.FiniteType R B] :
    ∃ U : (Spec R).Opens, Dense U.carrier ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ U) := by
  let ι := {r : R // Module.Free (Localization.Away r) (Localization.Away r ⊗[R] B)}
  let V (i : ι) : (Spec R).Opens := PrimeSpectrum.basicOpen i.1
  let U := ⨆ i, V i
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  refine ⟨U, dense_iff_inter_open.mpr ?_, ?_⟩
  · rintro W hW ⟨x, hx⟩
    obtain ⟨_, ⟨r, rfl⟩, hxr, hrW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hW
    have hr : ¬ IsNilpotent r := by
      intro hn
      have hb := (PrimeSpectrum.basicOpen_eq_bot_iff r).mpr hn
      change x ∈ PrimeSpectrum.basicOpen r at hxr
      rw [hb] at hxr
      exact hxr
    obtain ⟨s, hsr, ⟨y, hy⟩, hfree⟩ := exists_free_basicOpen_subset R B r hr
    exact ⟨y, hrW (hsr hy), (le_iSup V ⟨s, hfree⟩) hy⟩
  · refine flat_restrict_iSup f V fun i => ?_
    let : Module.Free (Localization.Away i.1) (Localization.Away i.1 ⊗[R] B) := i.2
    exact flat_restrict_basicOpen_of_free i.1

set_option backward.isDefEq.respectTransparency false in
private theorem exists_dense_open_flat_restrict_of_isAffine
    {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}} [IsNoetherianRing R] [IsReduced R]
    (f : X ⟶ Spec R) [LocallyOfFiniteType f] :
    ∃ U : (Spec R).Opens, Dense U.carrier ∧ Flat (f ∣_ U) := by
  let g := X.isoSpec.inv ≫ f
  let φ := Spec.preimage g
  have hg : Spec.map φ = g := Spec.map_preimage g
  let : Algebra R Γ(X, ⊤) := φ.hom.toAlgebra
  have hφ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    (hg ▸ (inferInstance : LocallyOfFiniteType g))
  let : Algebra.FiniteType R Γ(X, ⊤) := hφ
  obtain ⟨U, hU, hflat⟩ := exists_dense_open_flat_restrict_specMap_of_finiteType
    R Γ(X, ⊤)
  change Flat (Spec.map φ ∣_ U) at hflat
  rw [hg, morphismRestrict_comp] at hflat
  exact ⟨U, hU, (MorphismProperty.cancel_left_of_respectsIso @Flat
    (X.isoSpec.inv ∣_ f ⁻¹ᵁ U) (f ∣_ U)).mp hflat⟩

set_option backward.isDefEq.respectTransparency false in
/--
概要：準コンパクトな始域から被約 Noether アフィン基底への局所有限型射は稠密開上で平坦。
方針：始域の有限アフィン開被覆の各項で一般自由性を使い、得られた基底の開集合を交わらせる。
規約：準コンパクト性は始域の位相空間に対する仮定。
使われ方：BS17 Lemma 2.6 の固有射に対し、アフィン基底上で平坦開を選ぶ。
-/
theorem exists_dense_open_flat_restrict_of_compactSpace
    {X : Scheme.{u}} [CompactSpace X] {R : CommRingCat.{u}} [IsNoetherianRing R] [IsReduced R]
    (f : X ⟶ Spec R) [LocallyOfFiniteType f] :
    ∃ U : (Spec R).Opens, Dense U.carrier ∧ Flat (f ∣_ U) := by
  let 𝒰 := X.affineCover.finiteSubcover
  have h (i : 𝒰.I₀) :
      ∃ U : (Spec R).Opens, Dense U.carrier ∧ Flat ((𝒰.f i ≫ f) ∣_ U) := by
    have : IsAffine (𝒰.X i) := by
      rw [X.affineCover.finiteSubcover_X]
      exact Scheme.isAffine_affineCover X _
    exact exists_dense_open_flat_restrict_of_isAffine (𝒰.f i ≫ f)
  choose V hV hflat using h
  let U := ⨅ i, V i
  refine ⟨U, ?_, ?_⟩
  · rw [show U.carrier = ⋂ i, (V i).carrier from TopologicalSpace.Opens.coe_iInf V,
      ← Set.sInter_range]
    exact (Set.finite_range _).dense_sInter
      (Set.forall_mem_range.mpr fun i => (V i).isOpen) (Set.forall_mem_range.mpr hV)
  · apply IsZariskiLocalAtSource.of_openCover (P := @Flat) (𝒰.restrict (f ⁻¹ᵁ U))
    intro i
    rw [Scheme.OpenCover.restrict_f, ← morphismRestrict_comp]
    let g := 𝒰.f i ≫ f
    let W := (V i).ι ⁻¹ᵁ U
    have hW : (V i).ι ''ᵁ W = U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr (iInf_le V i)]
    rw [← MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictRestrict g (V i) W ≪≫ morphismRestrictEq g hW)]
    let : Flat (g ∣_ V i) := hflat i
    exact inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
概要：被約局所 Noether 基底上の有限型射は、基底の稠密開上で平坦。
方針：基底をアフィン開で覆い、各項で得た稠密平坦開の像の和を取る。
規約：始域の準コンパクト性は各基底アフィン開の逆像で用いる。
使われ方：BS17 Lemma 2.6 で固有全射に対する平坦化の外側の開を選ぶ。
-/
theorem exists_dense_open_flat_restrict_of_finiteType
    {X Y : Scheme.{u}} [_root_.AlgebraicGeometry.IsReduced Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFiniteType f] :
    ∃ U : Y.Opens, Dense U.carrier ∧ Flat (f ∣_ U) := by
  let 𝒰 := Y.affineCover
  let A (i : 𝒰.I₀) := (𝒰.f i).opensRange
  have hA (i : 𝒰.I₀) : IsAffineOpen (A i) := by
    have := Scheme.isAffine_affineCover Y i
    exact isAffineOpen_opensRange (𝒰.f i)
  have h (i : 𝒰.I₀) : ∃ W : (A i).toScheme.Opens,
      Dense W.carrier ∧ Flat (f ∣_ (A i).ι ''ᵁ W) := by
    let : IsAffine (A i).toScheme := hA i
    let e := (hA i).isoSpec
    let g := f ∣_ A i
    let : IsNoetherianRing Γ(Y, A i) :=
      IsLocallyNoetherian.component_noetherian ⟨A i, hA i⟩
    let : CompactSpace (f ⁻¹ᵁ A i).toScheme := QuasiCompact.compactSpace_of_compactSpace g
    obtain ⟨V, hV, hflat⟩ := exists_dense_open_flat_restrict_of_compactSpace (g ≫ e.hom)
    let W := e.hom ⁻¹ᵁ V
    refine ⟨W, hV.preimage (e.hom.homeomorph.isOpenMap), ?_⟩
    rw [morphismRestrict_comp,
      MorphismProperty.cancel_right_of_respectsIso @Flat (g ∣_ W) (e.hom ∣_ V)] at hflat
    exact (MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictRestrict f (A i) W)).mp hflat
  choose W hd hflat using h
  let V (i : 𝒰.I₀) := (A i).ι ''ᵁ W i
  refine ⟨⨆ i, V i, dense_iff_inter_open.mpr ?_, flat_restrict_iSup f V hflat⟩
  rintro T hT ⟨x, hx⟩
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  let z : A i := ⟨𝒰.f i y, ⟨y, rfl⟩⟩
  obtain ⟨w, hwT, hwW⟩ := dense_iff_inter_open.mp (hd i) ((A i).ι ⁻¹' T)
    ((A i).ι.continuous.isOpen_preimage _ hT) ⟨z, hx⟩
  exact ⟨(A i).ι w, hwT, (le_iSup V i) ⟨w, hwW, rfl⟩⟩

end SerrePositivity.AlgebraicGeometry
