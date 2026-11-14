module

public import SerrePositivity.AlgebraicGeometry.AffineOpenClosure
public import SerrePositivity.AlgebraicGeometry.FiniteTypeStrictTransformLocality

/-!
概要：基底のアフィン試験環で、狭義変換の平坦性を元の始域のアフィン開被覆で調べる。
方針：始域被覆を引き戻し、主開のスキーム論的閉包を純変換で計算する。
規約：元の射は局所有限型かつ準コンパクト。固有性は要求しない。
使われ方：有限型射の狭義変換を、有限型アフィン加群の平坦化に帰着する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
-- 開被覆のアフィン引き戻しと二つの周辺ファイバー積を比較する。
/--
概要：始域の全アフィン開で構造層の純変換が平坦なら、試験環上の狭義変換は平坦。
方針：周辺ファイバー積を始域のアフィン開で覆い、各アフィンの閉包を環の商で計算する。
規約：境界は基底の主開。試験環は Noether とする。
使われ方：ブローアップの標準チャートごとの狭義変換の平坦性。
-/
theorem flat_openImage_pullback_of_affineSourceCover_of_finiteType
    {R A : CommRingCat.{u}} [IsNoetherianRing A] [Algebra R A]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [LocallyOfFiniteType f] [QuasiCompact f]
    (𝒰 : X.AffineOpenCover) (t : R)
    (h : ∀ i, letI : Algebra R (𝒰.X i) := (Spec.preimage (𝒰.f i ≫ f)).hom.toAlgebra
      Module.Flat A (modulePureTransform (algebraMap R A t) (A ⊗[R] (𝒰.X i)))) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let q := pullback.snd f g
    Flat ((q ⁻¹ᵁ PrimeSpectrum.basicOpen (algebraMap R A t)).ι.imageι ≫ q) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let q := pullback.snd f g
  let r := pullback.fst f g
  let W := q ⁻¹ᵁ PrimeSpectrum.basicOpen (algebraMap R A t)
  let : _root_.AlgebraicGeometry.IsNoetherian (pullback f g) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian q
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace q }
  let 𝒱 : (pullback f g).OpenCover := 𝒰.openCover.pullback₁ r
  change Flat (W.ι.imageι ≫ q)
  apply flat_openImage_comp_of_flat_source_cover W q 𝒱.f
    (fun i => inferInstanceAs (Flat (𝒱.f i))) 𝒱.exists_eq
  intro i
  let B := 𝒰.X i
  let u := 𝒰.f i
  let p := 𝒱.f i
  let φ := Spec.preimage (u ≫ f)
  let : Algebra R B := φ.hom.toAlgebra
  let D := CommRingCat.of (A ⊗[R] B)
  let l := Spec.map (CommRingCat.ofHom (algebraMap A D))
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R B)) = u ≫ f := Spec.map_preimage _
  let e : Spec D ≅ 𝒱.X i :=
    (pullbackSpecIso R A B).symm ≪≫ pullback.congrHom rfl hφ ≪≫
      pullbackSymmetry g (u ≫ f) ≪≫ (pullbackRightPullbackFstIso f g u).symm ≪≫
      pullbackSymmetry u r
  have he : e.hom ≫ p ≫ q = l := by
    change e.hom ≫ pullback.fst r u ≫ pullback.snd f g = l
    simp [e, r, l, pullback.congrHom_hom, pullback.map]
    rw [pullback.lift_fst]
    exact pullbackSpecIso_inv_fst' R A B
  let W' := p ⁻¹ᵁ W
  have hW' : e.hom ⁻¹ᵁ W' = PrimeSpectrum.basicOpen (algebraMap A D (algebraMap R A t)) := by
    change e.hom ⁻¹ᵁ p ⁻¹ᵁ q ⁻¹ᵁ PrimeSpectrum.basicOpen (algebraMap R A t) = _
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Category.assoc, he, SpecMap_preimage_basicOpen]
    rfl
  change Flat (W'.ι.imageι ≫ p ≫ q)
  rw [← flat_openImage_comp_iso_iff W' e (p ≫ q), he]
  apply (flat_basicOpen_image_comp_specMap_iff A D (algebraMap R A t) _ hW').mpr
  exact h i

end SerrePositivity.AlgebraicGeometry
