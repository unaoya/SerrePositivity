module

public import SerrePositivity.AlgebraicGeometry.AffineOpenClosure
public import SerrePositivity.AlgebraicGeometry.StrictTransformLocality
public import SerrePositivity.AlgebraicGeometry.BlowupOpenComparison
public import SerrePositivity.AlgebraicGeometry.ChartGluing

/-!
概要：アフィン基底の主開に関する狭義変換の平坦性を標準ブローアップチャートで判定する。
方針：周辺ファイバー積をテンソル積の Spec と同定し、主開のスキーム論的閉包を計算する。
規約：チャート環の係数写像は chartBaseMap。
使われ方：有限加群の純変換を平坦にする中心を、スキームの平坦化に使う。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

private abbrev specBlowupChartι {R : CommRingCat.{u}} (J : (Spec R).IdealSheafData)
    (b : specIdealEquiv R (J.comap (𝟙 (Spec R)))) :
    Spec (.of (BlowupChartRing _ b)) ⟶ blowup J :=
  affineBlowupChartι _ b ≫ blowupAffineOpenMap (𝟙 (Spec R)) J

set_option backward.isDefEq.respectTransparency false in
private def specBlowupOpenCover (R : CommRingCat.{u}) (J : (Spec R).IdealSheafData) :
    (blowup J).OpenCover := by
  let K := specIdealEquiv R (J.comap (𝟙 (Spec R)))
  let X (b : K) := Spec (.of (BlowupChartRing K b))
  let g (b : K) : X b ⟶ blowup J := specBlowupChartι (R := R) J b
  have hcover : ∀ x : blowup J, ∃ (b : K) (z : X b), g b z = x := by
    intro x
    let j := blowupAffineOpenMap (𝟙 (Spec R)) J
    have hx : x ∈ Set.range j := by
      dsimp only [j]
      rw [blowupAffineOpenMap_range]
      simp
    obtain ⟨y, hy⟩ := hx
    let 𝒰 := affineBlowupChartCover K
    let b : K := 𝒰.idx y
    obtain ⟨z, hz⟩ := 𝒰.covers y
    have hz' : affineBlowupChartι K b z = y := hz
    exact ⟨b, z, (congrArg j hz').trans hy⟩
  have hopen (b : K) : IsOpenImmersion (g b) := by
    change IsOpenImmersion (affineBlowupChartι K b ≫ blowupAffineOpenMap (𝟙 (Spec R)) J)
    infer_instance
  exact Scheme.Cover.mkOfCovers (X := blowup J) (P := @IsOpenImmersion) K X g hcover hopen

set_option backward.isDefEq.respectTransparency false in
private theorem specBlowupChart_base {R : CommRingCat.{u}} (J : (Spec R).IdealSheafData)
    (b : specIdealEquiv R (J.comap (𝟙 (Spec R)))) :
    specBlowupChartι J b ≫ blowupπ J =
      Spec.map (CommRingCat.ofHom (chartBaseMap _ b)) := by
  rw [Category.assoc, blowupAffineOpenMap_base]
  let K := specIdealEquiv R (J.comap (𝟙 (Spec R)))
  exact (congrArg (affineBlowupChartι K b ≫ ·) (Category.comp_id (affineBlowupπ K))).trans
    (affineBlowupChartIso_inv_ι_π K b)

set_option backward.isDefEq.respectTransparency false in
private theorem flat_openImage_on_specChart_iff {R A B : CommRingCat.{u}}
    [IsNoetherianRing R] [Algebra R A] [Algebra R B]
    [IsProper (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (J : (Spec R).IdealSheafData) (t : R) (g : Spec A ⟶ blowup J) [IsOpenImmersion g]
    (hg : g ≫ blowupπ J = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := pullback.snd f (blowupπ J)
    Flat ((pullback.fst p g ⁻¹ᵁ strictTransformOpen f (PrimeSpectrum.basicOpen t) J).ι.imageι ≫
      pullback.snd p g) ↔ Module.Flat A (modulePureTransform (algebraMap R A t) (A ⊗[R] B)) := by
  dsimp only
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let π := blowupπ J
  let p := pullback.snd f π
  let q := pullback.snd p g
  let r := pullback.fst p g
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen t
  let V := strictTransformOpen f U J
  let W := r ⁻¹ᵁ V
  let D := CommRingCat.of (A ⊗[R] B)
  let a := Spec.map (CommRingCat.ofHom (algebraMap A D))
  let e : Spec D ≅ pullback p g :=
    (pullbackSpecIso R A B).symm ≪≫ pullback.congrHom hg.symm rfl ≪≫
      pullbackSymmetry (g ≫ π) f ≪≫ (pullbackLeftPullbackSndIso f π g).symm
  have heq : e.hom ≫ q = a := by
    simp [e, q, a, p, π, f]
    rfl
  have hW : e.hom ⁻¹ᵁ W = PrimeSpectrum.basicOpen (algebraMap A D (algebraMap R A t)) := by
    change e.hom ⁻¹ᵁ r ⁻¹ᵁ strictTransformOpen f U J = _
    simp only [strictTransformOpen_eq, ← Scheme.Hom.comp_preimage]
    have hpr : r ≫ p = q ≫ g := pullback.condition
    have hprπ : r ≫ p ≫ π = q ≫ g ≫ π := by
      simpa only [Category.assoc] using congrArg (fun l => l ≫ π) hpr
    change (e.hom ≫ r ≫ p ≫ π) ⁻¹ᵁ U = _
    rw [hprπ, ← Category.assoc e.hom q, heq, hg, Scheme.Hom.comp_preimage,
      SpecMap_preimage_basicOpen, SpecMap_preimage_basicOpen]
    rfl
  have : QuasiCompact V.ι := inferInstance
  have : QuasiCompact W.ι := MorphismProperty.of_isPullback (isPullback_morphismRestrict r V)
    inferInstance
  change Flat (W.ι.imageι ≫ q) ↔ _
  rw [← flat_openImage_comp_iso_iff W e q, heq]
  exact flat_basicOpen_image_comp_specMap_iff A D (algebraMap R A t) _ hW

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether アフィン基底上の固有アフィン射の狭義変換は、各標準チャートの純変換が平坦なら平坦。
方針：一般ブローアップを標準チャートで覆い、各チャートの周辺ファイバー積をテンソル積で表示する。
規約：基底の開集合は主開。狭義変換は既存の幾何学的構成を使う。
使われ方：有限加群の平坦化中心から、有限射の狭義変換の平坦化を得る。
-/
theorem flat_strictTransformπ_specMap_of_chartPureTransform
    (R B : CommRingCat.{u}) [IsNoetherianRing R] [Algebra R B]
    [IsProper (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (t : R) (I : Ideal R)
    (h : ∀ b : I, letI : Algebra R (BlowupChartRing I b) := (chartBaseMap I b).toAlgebra
      Module.Flat (BlowupChartRing I b)
        (modulePureTransform (chartBaseMap I b t) (BlowupChartRing I b ⊗[R] B))) :
    Flat (strictTransformπ (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (PrimeSpectrum.basicOpen t) ((specIdealEquiv R).symm I)) := by
  let J := (specIdealEquiv R).symm I
  let 𝒱 := specBlowupOpenCover R J
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  change Flat (strictTransformπ f (PrimeSpectrum.basicOpen t) J)
  refine (flat_strictTransformπ_iff_of_openCover f (PrimeSpectrum.basicOpen t) J 𝒱).mpr ?_
  let K := specIdealEquiv R (J.comap (𝟙 (Spec R)))
  have hK : K = I := by
    change specIdealEquiv R (J.comap (𝟙 _)) = I
    rw [Scheme.IdealSheafData.comap_id, OrderIso.apply_symm_apply]
  have hKflat : ∀ b : K, letI : Algebra R (BlowupChartRing K b) := (chartBaseMap K b).toAlgebra
      Module.Flat (BlowupChartRing K b)
        (modulePureTransform (chartBaseMap K b t) (BlowupChartRing K b ⊗[R] B)) := by
    rw [hK]
    exact h
  intro b
  let A := CommRingCat.of (BlowupChartRing K b)
  let : Algebra R A := (chartBaseMap K b).toAlgebra
  let g : Spec A ⟶ blowup J := 𝒱.f b
  have hg := specBlowupChart_base (R := R) J b
  let H := flat_openImage_on_specChart_iff (R := R) (A := A) (B := B) J t g hg
  exact H.mpr (hKflat b)

end SerrePositivity.AlgebraicGeometry
