module

public import SerrePositivity.AlgebraicGeometry.AdmissibleRefinement
public import SerrePositivity.AlgebraicGeometry.BlowupSchemeDensity
public import SerrePositivity.AlgebraicGeometry.FiniteTypeFlatClosurePullback
public import SerrePositivity.AlgebraicGeometry.LocalDominationRestriction

/-!
概要：アフィン局所で狭義変換を平坦にする中心を、一つの基底中心にまとめる。
方針：各局所中心を大域に押し出して共通細分を取り、稠密な境界開に沿って平坦性を保存する。
規約：中心の補開集合を指定された境界に一致させる。
使われ方：最初の許容ブローアップの正則主開の被覆から、二段目の中心を構成する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
-- 局所の基底変更と共通細分の二段の射の交換式を照合する。
/--
概要：基底の有限アフィン開被覆で狭義変換を平坦化できれば、基底全体を許容ブローアップで平坦化できる。
方針：大域へ移した局所中心の共通細分を選び、狭義変換の平坦性をその開被覆で確かめる。
規約：基底は Noether、射は局所有限型かつ準コンパクト。
使われ方：一般の平坦開を使う有限型射の中心の貼り合わせ。
-/
theorem exists_admissible_flat_strictTransformπ_of_affine_local_of_finiteType
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (U : S.Opens)
    (𝒰 : S.AffineOpenCover) [Finite 𝒰.I₀]
    (J : ∀ i, (Spec (𝒰.X i)).IdealSheafData)
    (hJ : ∀ i, IsUAdmissibleCenter (𝒰.f i ⁻¹ᵁ U) (J i))
    (hflat : ∀ i, Flat (strictTransformπ (pullback.snd f (𝒰.f i)) (𝒰.f i ⁻¹ᵁ U) (J i))) :
    ∃ K : S.IdealSheafData, centerComplement K = U ∧ Flat (strictTransformπ f U K) := by
  classical
  let N (i : 𝒰.I₀) := (J i).map (𝒰.f i)
  have hN (i : 𝒰.I₀) : IsUAdmissibleCenter U (N i) :=
    isUAdmissibleCenter_map (𝒰.f i) U (J i) (hJ i)
  obtain ⟨K, hKU, _, hdom⟩ := exists_admissible_family_refinement U N hN
  choose τ hτ using hdom
  let p := blowupπ K
  let W (i : 𝒰.I₀) := p ⁻¹ᵁ (𝒰.f i).opensRange
  have hW : (⨆ i, W i) = ⊤ := by
    apply top_unique
    intro x _
    have hx : p x ∈ (⨆ i, (𝒰.f i).opensRange) := by
      rw [show (⨆ i, (𝒰.f i).opensRange) = ⊤ from 𝒰.openCover.iSup_opensRange]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let 𝒱 := Scheme.openCoverOfIsOpenCover (blowup K) W hW
  let V := p ⁻¹ᵁ U
  let : IsSchemeTheoreticallyDominant V.ι := by
    change IsSchemeTheoreticallyDominant (blowupπ K ⁻¹ᵁ U).ι
    rw [← hKU]
    exact blowup_centerComplement_isSchemeTheoreticallyDominant K
  refine ⟨K, hKU, (flat_strictTransformπ_iff_of_openCover_of_finiteType f U K 𝒱).mpr ?_⟩
  intro i
  change 𝒰.I₀ at i
  let A := 𝒰.X i
  let u := 𝒰.f i
  let q := blowupπ (J i) ≫ u
  let L := specIdealEquiv A ((N i).comap u)
  let L' := specIdealEquiv A ((J i).comap (𝟙 (Spec A)))
  have hL : L = L' := by
    change specIdealEquiv A (((J i).map u).comap u) =
      specIdealEquiv A ((J i).comap (𝟙 (Spec A)))
    rw [idealSheaf_comap_map_openImmersion, Scheme.IdealSheafData.comap_id]
  let g := eqToHom (congrArg affineBlowup hL) ≫ blowupAffineOpenMap (𝟙 (Spec A)) (J i)
  have hg : g ≫ q = affineBlowupπ L ≫ u := by
    have hπ : blowupAffineOpenMap (𝟙 (Spec A)) (J i) ≫ blowupπ (J i) = affineBlowupπ L' :=
      (blowupAffineOpenMap_base (𝟙 (Spec A)) (J i)).trans (Category.comp_id _)
    calc
      _ = eqToHom (congrArg affineBlowup hL) ≫
          (blowupAffineOpenMap (𝟙 (Spec A)) (J i) ≫ blowupπ (J i)) ≫ u := by
        simp only [g, q, Category.assoc]
      _ = _ := by rw [hπ, affineBlowup_eqToHom_base_assoc L L' hL]
  let v := localDominationRestriction K (N i) u (τ i) (hτ i) g
  have hv : v ≫ q = (W i).ι ≫ p :=
    localDominationRestriction_base K (N i) u (τ i) (hτ i) q g hg
  let : _root_.AlgebraicGeometry.IsNoetherian (W i).toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace :=
        isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _) }
  let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion u)
  let : IsSchemeTheoreticallyDominant (v ⁻¹ᵁ q ⁻¹ᵁ U).ι := by
    rw [← Scheme.Hom.comp_preimage, hv, Scheme.Hom.comp_preimage]
    exact IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (W i).ι V)
  have hq : HasFlatOpenClosure f U q := (hasFlatOpenClosure_comp_iff_of_finiteType f U u (blowupπ (J i))).mpr
    ((hasFlatOpenClosure_blowup_iff _ _ _).mpr (hflat i))
  have h := hq.comp_of_dominant_of_finiteType v
  rw [hv] at h
  have hh := (hasFlatOpenClosure_comp_iff_of_finiteType f U p (W i).ι).mp h
  change Flat (((pullback.snd (pullback.snd f p) (W i).ι) ⁻¹ᵁ (W i).ι ⁻¹ᵁ V).ι.imageι ≫
    pullback.snd (pullback.snd f p) (W i).ι) at hh
  change Flat (((pullback.fst (pullback.snd f p) (W i).ι) ⁻¹ᵁ
    strictTransformOpen f U K).ι.imageι ≫ pullback.snd (pullback.snd f p) (W i).ι)
  rw [strictTransformOpen_eq, ← Scheme.Hom.comp_preimage, pullback.condition,
    Scheme.Hom.comp_preimage]
  exact hh

end SerrePositivity.AlgebraicGeometry
