module

public import SerrePositivity.AlgebraicGeometry.AdmissibleRefinement
public import SerrePositivity.AlgebraicGeometry.AffineFiberSupportFlattening
public import SerrePositivity.AlgebraicGeometry.DensePrincipalOpen
public import SerrePositivity.AlgebraicGeometry.FiniteAffineCover
public import SerrePositivity.AlgebraicGeometry.GenericFlatness
public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback
public import SerrePositivity.AlgebraicGeometry.ProperFlatBlowupRefinement
public import SerrePositivity.AlgebraicGeometry.FiniteTypeStrictTransformFlatPure
public import SerrePositivity.CommutativeAlgebra.Localization.Away

/-!
概要：アフィン基底上の有限型射を許容ブローアップと fppf 射で細分する。
方針：始域の有限アフィン開被覆で構造層を平坦化し、基底の共通中心で狭義変換の平坦性を得る。
規約：基底は Noether で、稠密平坦開は被約基底上の一般平坦性で選べる。
使われ方：BS17 Lemma 2.6 でアフィン基底上の固有全射を細分する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
-- 有限個のアフィンチャートの係数写像を共通のブローアップへ移す。
/--
概要：Noether アフィン基底上の有限型射が正則な主開上で平坦なら、許容中心で狭義変換を平坦化できる。
方針：始域の有限アフィン開ごとに有限型加群を平坦化し、すべての局所中心を支配する中心を選ぶ。
規約：始域のアフィン性・射の固有性を仮定しない。
使われ方：有限型射の fppf 細分。
-/
theorem exists_admissible_flat_strictTransformπ_finiteType_affineBase
    {R : CommRingCat.{u}} [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec R) [LocallyOfFiniteType f] [QuasiCompact f]
    (a : R) (ha : IsRegular a) (h : Flat (f ∣_ PrimeSpectrum.basicOpen a)) :
    ∃ J : (Spec R).IdealSheafData, IsUAdmissibleCenter (PrimeSpectrum.basicOpen a) J ∧
      Flat (strictTransformπ f (PrimeSpectrum.basicOpen a) J) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨𝒰, h𝒰⟩ := exists_finite_affineOpenCover X
  let : Finite 𝒰.I₀ := h𝒰
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen a
  have hlocal (i : 𝒰.I₀) :
      letI : Algebra R (𝒰.X i) := (Spec.preimage (𝒰.f i ≫ f)).hom.toAlgebra
      ∃ I : Ideal R, PrimeSpectrum.basicOpen a ≤ affineCenterComplement I ∧
        HasFlatPurePullbacks (affineBlowupπ I) a (𝒰.X i) := by
    let B := 𝒰.X i
    let g := 𝒰.f i
    let φ := Spec.preimage (g ≫ f)
    let : Algebra R B := φ.hom.toAlgebra
    have hφ : Spec.map φ = g ≫ f := Spec.map_preimage _
    let : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstanceAs (LocallyOfFiniteType (g ≫ f))
    let : Algebra.FiniteType R B :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
    have hD : Flat (Spec.map φ ∣_ U) := by
      rw [hφ, morphismRestrict_comp]
      let : Flat (f ∣_ U) := h
      infer_instance
    have hB : Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] B) := by
      rw [MorphismProperty.arrow_mk_iso_iff @Flat (SpecMapRestrictBasicOpenIso φ a),
        Flat.SpecMap_iff] at hD
      let := SerrePositivity.GenericEtale.awayAlgebra R B a
      change Module.Flat (Localization.Away a) (Localization.Away (algebraMap R B a)) at hD
      exact Module.Flat.of_linearEquiv
        (SerrePositivity.originalAwayTensorEquiv R B a).toLinearEquiv
    obtain ⟨I, _, hI, hflat⟩ := exists_affine_flatPure_center_of_finiteType (B := B) a ha hB
    exact ⟨I, hI, hflat⟩
  choose I hI hflat using hlocal
  let J (i : 𝒰.I₀) := (specIdealEquiv R).symm (I i)
  have hJ (i : 𝒰.I₀) : IsUAdmissibleCenter U (J i) := by
    change U ≤ centerComplement (J i)
    rw [centerComplement_specIdealEquiv, show specIdealEquiv R (J i) = I i from
      (specIdealEquiv R).apply_symm_apply _]
    exact hI i
  obtain ⟨K, hK, _, hdom⟩ := exists_admissible_family_refinement U J hJ
  refine ⟨K, hK.ge, flat_strictTransformπ_of_flatPurePullbacks_affineCover_of_finiteType f 𝒰 a ha K ?_⟩
  intro i
  let : Algebra R (𝒰.X i) := (Spec.preimage (𝒰.f i ≫ f)).hom.toAlgebra
  obtain ⟨g, hg⟩ := hdom i
  let s := blowupAffineOpenMap (𝟙 (Spec R)) (J i)
  let : IsIso s := isIso_blowupAffineOpenMap_id (J i)
  let L := specIdealEquiv R ((J i).comap (𝟙 (Spec R)))
  have hL : L = I i := by
    change specIdealEquiv R ((J i).comap (𝟙 (Spec R))) = I i
    rw [Scheme.IdealSheafData.comap_id, show specIdealEquiv R (J i) = I i from
      (specIdealEquiv R).apply_symm_apply _]
  have hs : s ≫ blowupπ (J i) = affineBlowupπ L :=
    (blowupAffineOpenMap_base (𝟙 (Spec R)) (J i)).trans (Category.comp_id _)
  have hq : (g ≫ inv s) ≫ affineBlowupπ L = blowupπ K := by
    rw [Category.assoc, ← hs, IsIso.inv_hom_id_assoc, hg]
  have hp : HasFlatPurePullbacks (affineBlowupπ L) a (𝒰.X i) := hL.symm ▸ hflat i
  exact hq ▸ hp.comp (g ≫ inv s)


end SerrePositivity.AlgebraicGeometry
