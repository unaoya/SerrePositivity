module

public import SerrePositivity.AlgebraicGeometry.BlowupChartIdeals
public import SerrePositivity.AlgebraicGeometry.BlowupOpenComparison
public import SerrePositivity.AlgebraicGeometry.ChartBoundaryRegular
public import SerrePositivity.AlgebraicGeometry.PureTransformPullbacks
public import SerrePositivity.AlgebraicGeometry.FiniteTypeStrictTransformAffineSource
public import SerrePositivity.AlgebraicGeometry.StrictTransformFlatFromPurePullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
概要：アフィン基底上の有限型射の狭義変換を、始域のアフィン開の純変換で平坦化する。
方針：基底のブローアップを標準アフィンチャートで覆い、各チャートで始域被覆の構造層を使う。
規約：射は局所有限型かつ準コンパクトとし、固有性は課さない。
使われ方：有限型加群の平坦化中心を、有限型射の細分に渡す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/-- pullback の底辺の等式による比較は、第二射影と可換。 -/
private theorem finiteType_congrHom_hom_snd {X Y T : Scheme.{u}} (f : X ⟶ Y)
    {g h : T ⟶ Y} (e : g = h) :
    (pullback.congrHom (f₁ := f) rfl e).hom ≫ pullback.snd f h = pullback.snd f g := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency false in
-- 標準チャート上の引き戻しと構造層の二つの係数写像を照合する。
/--
概要：始域のアフィン開被覆すべてで純変換の引き戻しが平坦なら、ブローアップ上の狭義変換は平坦。
方針：標準チャートでは境界の正則性が保たれるため、仮定を実際のチャート環へ適用する。
規約：基底は Noether アフィンで、境界は正則な一元で与える。
使われ方：アフィン基底上の一般の固有射を許容ブローアップで平坦化する。
-/
theorem flat_strictTransformπ_of_flatPurePullbacks_affineCover_of_finiteType
    {R : CommRingCat.{u}} [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec R) [LocallyOfFiniteType f] [QuasiCompact f]
    (𝒰 : X.AffineOpenCover) (a : R) (ha : IsRegular a) (J : (Spec R).IdealSheafData)
    (h : ∀ i, letI : Algebra R (𝒰.X i) := (Spec.preimage (𝒰.f i ≫ f)).hom.toAlgebra
      HasFlatPurePullbacks (blowupπ J) a (𝒰.X i)) :
    Flat (strictTransformπ f (PrimeSpectrum.basicOpen a) J) := by
  let I := specIdealEquiv R (J.comap (𝟙 (Spec R)))
  let j := blowupAffineOpenMap (𝟙 (Spec R)) J
  let : IsIso j := isIso_blowupAffineOpenMap_id J
  let 𝒱 : (blowup J).OpenCover := (affineBlowupChartCover I).openCover.pushforwardIso j
  apply (flat_strictTransformπ_iff_of_openCover_of_finiteType f (PrimeSpectrum.basicOpen a) J 𝒱).mpr
  intro b
  change I at b
  let A := CommRingCat.of (BlowupChartRing I b)
  let φ := chartBaseMap I b
  let : IsNoetherianRing A := blowupChartRing_isNoetherianRing I b
  let : Algebra R A := φ.toAlgebra
  let g : Spec A ⟶ blowup J := 𝒱.f b
  let π := blowupπ J
  have hg : g ≫ π = Spec.map (CommRingCat.ofHom φ) := by
    change (affineBlowupChartι I b ≫ j) ≫ π = _
    have hπ : j ≫ π = affineBlowupπ I :=
      (blowupAffineOpenMap_base (𝟙 (Spec R)) J).trans (Category.comp_id _)
    rw [Category.assoc, hπ]
    exact affineBlowupChartIso_inv_ι_π I b
  have hmap : pureTransformCoefficientMap π g = φ := by
    unfold pureTransformCoefficientMap
    rw [hg, Spec.preimage_map]
    rfl
  have hA (i : 𝒰.I₀) :
      letI : Algebra R (𝒰.X i) := (Spec.preimage (𝒰.f i ≫ f)).hom.toAlgebra
      Module.Flat A (modulePureTransform (algebraMap R A a) (A ⊗[R] (𝒰.X i))) := by
    let : Algebra R (𝒰.X i) := (Spec.preimage (𝒰.f i ≫ f)).hom.toAlgebra
    let P (ψ : R →+* A) : Prop :=
      letI : Algebra R A := ψ.toAlgebra
      IsRegular (ψ a) → Module.Flat A (modulePureTransform (ψ a) (A ⊗[R] (𝒰.X i)))
    exact (congrArg P hmap).mp (h i A g) (isRegular_iff_mem_nonZeroDivisors.mpr
      (chartBaseMap_nonZeroDivisors I b ha.mem_nonZeroDivisors))
  let p := pullback.snd f π
  let q := pullback.snd p g
  let r := pullback.fst p g
  let ψ := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hg' : g ≫ π = ψ := hg
  let q' := pullback.snd f ψ
  let e : pullback p g ≅ pullback f ψ :=
    pullbackLeftPullbackSndIso f π g ≪≫ pullback.congrHom rfl hg'
  have he : e.hom ≫ q' = q := by
    change ((pullbackLeftPullbackSndIso f π g).hom ≫ (pullback.congrHom rfl hg').hom) ≫
      pullback.snd f ψ = q
    rw [Category.assoc]
    exact (congrArg ((pullbackLeftPullbackSndIso f π g).hom ≫ ·)
      (finiteType_congrHom_hom_snd f hg')).trans (pullbackLeftPullbackSndIso_hom_snd f π g)
  let W := q' ⁻¹ᵁ PrimeSpectrum.basicOpen (algebraMap R A a)
  let : _root_.AlgebraicGeometry.IsNoetherian (pullback f ψ) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian q'
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace q' }
  have hW : e.hom ⁻¹ᵁ W = r ⁻¹ᵁ strictTransformOpen f (PrimeSpectrum.basicOpen a) J := by
    rw [strictTransformOpen_eq]
    change e.hom ⁻¹ᵁ q' ⁻¹ᵁ PrimeSpectrum.basicOpen (algebraMap R A a) =
      r ⁻¹ᵁ p ⁻¹ᵁ π ⁻¹ᵁ PrimeSpectrum.basicOpen a
    rw [← Scheme.Hom.comp_preimage e.hom q', he, ← Scheme.Hom.comp_preimage r p,
      show r ≫ p = q ≫ g from pullback.condition, Scheme.Hom.comp_preimage q g,
      ← Scheme.Hom.comp_preimage g π, hg, SpecMap_preimage_basicOpen]
    rfl
  have hflat := flat_openImage_pullback_of_affineSourceCover_of_finiteType f 𝒰 a hA
  have ht := (flat_openImage_comp_iso_iff W e q').mpr hflat
  rw [hW, he] at ht
  exact ht

end SerrePositivity.AlgebraicGeometry
