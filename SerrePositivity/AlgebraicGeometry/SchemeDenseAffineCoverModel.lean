module

public import SerrePositivity.AlgebraicGeometry.FiniteDenseAffineCover
public import SerrePositivity.AlgebraicGeometry.DenseImageOpenLifts
public import SerrePositivity.AlgebraicGeometry.ImmersionProperClosure

/-!
概要：Noether な既約スキームから、scheme-theoretic に稠密な共通の開を持つ affine 被覆模型を作る。
方針：共通の開の実際の像を取り、元の affine 被覆を閉全射に沿って引き戻す。
規約：内部データの存在は元の対象から無条件に供給する。
使われ方：C06 のグラフ閉包を各 affine チャートの閉包へ因子化する入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 共通の開から各 affine チャートへの実際の稠密な開包含を持つ、元の対象の閉全射模型。 -/
structure SchemeDenseAffineCoverModel (X : Scheme.{u}) where
  base : Scheme.{u}
  toBase : base ⟶ X
  toBase_closed : IsClosedImmersion toBase
  toBase_surjective : Surjective toBase
  base_noetherian : IsNoetherian base
  n : ℕ
  n_pos : 0 < n
  chart : Fin n → base.Opens
  chart_affine : ∀ i, IsAffineOpen (chart i)
  chart_cover : (⨆ i, chart i) = ⊤
  common : Scheme.{u}
  common_noetherian : IsNoetherian common
  common_nonempty : Nonempty common
  commonι : common ⟶ base
  common_open : IsOpenImmersion commonι
  common_dense : IsSchemeTheoreticallyDominant commonι
  toChart : ∀ i, common ⟶ (chart i).toScheme
  toChart_open : ∀ i, IsOpenImmersion (toChart i)
  toChart_dense : ∀ i, IsSchemeTheoreticallyDominant (toChart i)
  toChart_fac : ∀ i, toChart i ≫ (chart i).ι = commonι

/-- Noether な既約スキームから、実際の scheme-theoretic に稠密な affine 被覆模型を供給する。 -/
theorem exists_schemeDense_affine_cover_model (X : Scheme.{u})
    [IsNoetherian X] [IrreducibleSpace X] : Nonempty (SchemeDenseAffineCoverModel X) := by
  classical
  obtain ⟨n, hn, U, W, hAff, hne, hcover, hDense, hWne, hWi⟩ :=
    exists_dense_common_finite_affine_cover X
  let Z := W.ι.image
  let b : Z ⟶ X := W.ι.imageι
  let a : W.toScheme ⟶ Z := W.ι.toImage
  letI : CompactSpace W.toScheme := QuasiCompact.compactSpace_of_compactSpace W.ι
  letI : IsNoetherian W.toScheme := ⟨⟩
  letI : IsNoetherian Z := isNoetherian_schemeImage W.ι
  haveI : IsSchemeTheoreticallyDominant a := isSchemeTheoreticallyDominant_toImage W.ι
  haveI : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion W.ι.toImage)
  have hac : a ≫ b = W.ι := W.ι.toImage_imageι
  let V (i : Fin n) : Z.Opens := b ⁻¹ᵁ U i
  have haV (i : Fin n) : Set.range a ⊆ Set.range (V i).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change b (a w) ∈ U i
    rw [← Scheme.Hom.comp_apply, hac]
    exact hWi i w.property
  let l (i : Fin n) : W.toScheme ⟶ (V i).toScheme :=
    IsOpenImmersion.lift (V i).ι a (haV i)
  refine ⟨{
    base := Z
    toBase := b
    toBase_closed := inferInstance
    toBase_surjective := surjective_denseOpenImageInclusion W hDense
    base_noetherian := inferInstance
    n := n
    n_pos := hn
    chart := V
    chart_affine := fun i ↦ (hAff i).preimage b
    chart_cover := b.iSup_preimage_eq_top hcover
    common := W.toScheme
    common_noetherian := inferInstance
    common_nonempty := ⟨⟨hWne.choose, hWne.choose_spec⟩⟩
    commonι := a
    common_open := inferInstance
    common_dense := inferInstance
    toChart := l
    toChart_open := fun i ↦ isOpenImmersion_open_lift a (V i).ι (haV i)
    toChart_dense := fun i ↦ isSchemeTheoreticallyDominant_open_lift a (V i).ι (haV i)
    toChart_fac := fun i ↦ IsOpenImmersion.lift_fac (V i).ι a (haV i)
  }⟩

end SerrePositivity.AlgebraicGeometry
