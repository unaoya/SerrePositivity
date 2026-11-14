module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.AlgebraicGeometry.AffineStrictTransformFlatness
public import SerrePositivity.AlgebraicGeometry.DensePrincipalOpen
public import SerrePositivity.AlgebraicGeometry.GenericFlatness
public import SerrePositivity.AlgebraicGeometry.NoetherianFiniteModuleFlattening
public import SerrePositivity.AlgebraicGeometry.ProperFlatBlowupRefinement
public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback
public import SerrePositivity.CommutativeAlgebra.Localization.Away

/-!
概要：Noether アフィン基底上の有限射を、正則な主境界に沿って平坦化する。
方針：有限加群の平坦化中心をイデアル層に移し、標準チャートの純変換の平坦性を使う。
規約：主開上の平坦性はスキーム射の性質として入力する。
使われ方：BS17 Lemma 2.6 に使う平坦化の有限射の場合。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
private theorem flat_awayTensor_of_flat_restrict
    (R B : CommRingCat.{u}) [Algebra R B] (t : R)
    (h : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ PrimeSpectrum.basicOpen t)) :
    Module.Flat (Localization.Away t) (Localization.Away t ⊗[R] B) := by
  rw [MorphismProperty.arrow_mk_iso_iff @Flat
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap R B)) t), Flat.SpecMap_iff] at h
  let := SerrePositivity.GenericEtale.awayAlgebra R B t
  change Module.Flat (Localization.Away t) (Localization.Away (algebraMap R B t)) at h
  exact Module.Flat.of_linearEquiv
    (SerrePositivity.originalAwayTensorEquiv R B t).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether アフィン基底上の有限射が正則な主開上で平坦なら、許容ブローアップで平坦化できる。
方針：有限加群の平坦化定理が返す中心で、幾何学的な狭義変換の平坦性を示す。
規約：結論は実際の許容中心と、その狭義変換の構造射の平坦性。
使われ方：有限全射の proper fppf 細分。
-/
theorem exists_admissible_flat_strictTransformπ_of_finite
    (R B : CommRingCat.{u}) [IsNoetherianRing R] [Algebra R B] [Module.Finite R B]
    (t : R) (ht : t ∈ nonZeroDivisors R)
    (h : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ PrimeSpectrum.basicOpen t)) :
    ∃ J : (Spec R).IdealSheafData, IsUAdmissibleCenter (PrimeSpectrum.basicOpen t) J ∧
      Flat (strictTransformπ (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (PrimeSpectrum.basicOpen t) J) := by
  let φ := CommRingCat.ofHom (algebraMap R B)
  let : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  let L := Localization.Away t
  let : Module.Flat L (L ⊗[R] B) := flat_awayTensor_of_flat_restrict R B t h
  obtain ⟨I, _, hI, hflat⟩ := exists_noetherian_finite_flattening_center
    t ht B (TensorProduct.mk R L B 1)
  let J := (specIdealEquiv R).symm I
  refine ⟨J, ?_, flat_strictTransformπ_specMap_of_chartPureTransform R B t I hflat⟩
  change PrimeSpectrum.basicOpen t ≤ centerComplement J
  rwa [centerComplement_specIdealEquiv, OrderIso.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則な主開上で平坦な有限全射は、許容ブローアップと proper fppf 射で細分できる。
方針：有限射の平坦化中心に、固有全射の細分定理を適用する。
規約：proper fppf は固有・平坦・全射・局所有限表示の条件で返す。
使われ方：BS17 Lemma 2.6 の正次元での細分の有限射の場合。
-/
theorem exists_proper_fppf_blowup_refinement_of_finite
    (R B : CommRingCat.{u}) [IsNoetherianRing R] [Algebra R B] [Module.Finite R B]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (t : R) (ht : t ∈ nonZeroDivisors R)
    (h : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ PrimeSpectrum.basicOpen t)) :
    ∃ J : (Spec R).IdealSheafData,
      IsUAdmissibleCenter (PrimeSpectrum.basicOpen t) J ∧
      IsProper (blowupπ J) ∧ Surjective (blowupπ J) ∧
      IsIso (blowupπ J ∣_ PrimeSpectrum.basicOpen t) ∧
      ∃ (X' : Scheme.{u}) (g : X' ⟶ blowup J) (k : X' ⟶ Spec B),
        IsProper g ∧ Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
          k ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = g ≫ blowupπ J := by
  let φ := CommRingCat.ofHom (algebraMap R B)
  let : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  obtain ⟨J, hJ, hflat⟩ := exists_admissible_flat_strictTransformπ_of_finite R B t ht h
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen t
  have hd : Dense U.carrier := by
    change Dense (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum R))
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away t) t]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (IsLocalization.injective (Localization.Away t) (Submonoid.powers_le.mpr ht))]
    exact bot_le
  let : Flat (strictTransformπ (Spec.map φ) U J) := hflat
  exact ⟨J, hJ, exists_proper_fppf_blowup_refinement_of_flat_strictTransform
    (Spec.map φ) U J hd hJ⟩

set_option backward.isDefEq.respectTransparency false in
/--
概要：被約 Noether アフィン基底上の有限射に、正則な平坦主開と許容平坦化中心が存在する。
方針：一般平坦開を正則主開に縮めてから、有限加群の純変換を平坦化する。
規約：平坦開や中心は入力に含めない。
使われ方：有限射の場合の Noether 平坦化を一般平坦性につなぐ。
-/
theorem exists_admissible_flat_strictTransformπ_of_finite_of_isReduced
    (R B : CommRingCat.{u}) [IsNoetherianRing R] [IsReduced R]
    [Algebra R B] [Module.Finite R B] :
    ∃ t : R, t ∈ nonZeroDivisors R ∧
      ∃ J : (Spec R).IdealSheafData, IsUAdmissibleCenter (PrimeSpectrum.basicOpen t) J ∧
        Flat (strictTransformπ (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (PrimeSpectrum.basicOpen t) J) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  obtain ⟨U, hU, hflat⟩ := exists_dense_open_flat_restrict_specMap_of_finiteType R B
  obtain ⟨t, ht, hle⟩ := exists_nonZeroDivisor_basicOpen_le_of_dense R U hU
  let D : (Spec R).Opens := PrimeSpectrum.basicOpen t
  let V := U.ι ⁻¹ᵁ D
  have hV : U.ι ''ᵁ V = D := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hle]
  have hD : Flat (f ∣_ D) := (MorphismProperty.arrow_mk_iso_iff @Flat
    (morphismRestrictRestrict f U V ≪≫ morphismRestrictEq f hV)).mp
      (IsZariskiLocalAtTarget.restrict (P := @Flat) hflat V)
  exact ⟨t, ht, exists_admissible_flat_strictTransformπ_of_finite R B t ht hD⟩

end SerrePositivity.AlgebraicGeometry

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Proof step §5.2 flattening" (partial := component) "仮定：有限射の場合の平坦化、または既に与えた二段の許容ブローアップ（Lean が強い）。結論：有限射からの精密化と許容ブローアップの支配。一般の固有射の Temkin による支配を供給しない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.exists_proper_fppf_blowup_refinement_of_finite
attribute [cite LT "Proof step A.2 Step 3" (partial := component) "仮定：有限射、または既に与えられた二段の許容ブローアップ（Lean が強い）。結論：古典的な支配・平坦化の幾何の部品。切断型不変量に適用した引き戻しはない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.exists_proper_fppf_blowup_refinement_of_finite
