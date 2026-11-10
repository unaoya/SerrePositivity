module

public import SerrePositivity.AlgebraicGeometry.AffineIdealPullback
public import SerrePositivity.AlgebraicGeometry.BlowupChartIdeals
public import SerrePositivity.AlgebraicGeometry.ExactAffineAdmissibleComposition
public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback
public import SerrePositivity.AlgebraicGeometry.SchemeExceptional

/-!
概要：Noether スキームのブローアップ上で中心外の逆像を正則主開として表す。
方針：標準チャート上の拡大中心は一つの正則元で生成される。
規約：基底の中心はイデアル層で与える。
使われ方：稠密な平坦開の逆像が各アフィンチャートで主開となるよう、最初のブローアップを取る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether スキームのブローアップは、中心外の逆像が正則な主開となる有限アフィン被覆を持つ。
方針：中心の各アフィン切断の斉次チャートを取り、ブローアップの準コンパクト性で有限化する。
規約：チャート環は Noether 環として返す。
使われ方：一般の基底で正則な主境界の場合の平坦化を貼り合わせる。
-/
theorem exists_finite_affineOpenCover_blowup_principalBoundary
    {S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S] (I : S.IdealSheafData) :
    ∃ (𝒰 : Scheme.AffineOpenCover.{u, u} (blowup I)) (_ : Finite 𝒰.I₀),
      ∀ i, IsNoetherianRing (𝒰.X i) ∧
        ∃ a : 𝒰.X i, IsRegular a ∧
          𝒰.f i ⁻¹ᵁ blowupπ I ⁻¹ᵁ centerComplement I = PrimeSpectrum.basicOpen a := by
  classical
  let ι := Σ U : S.affineOpens, I.ideal U
  let B (i : ι) := CommRingCat.of (BlowupChartRing (I.ideal i.1) i.2)
  let g (i : ι) : Spec (B i) ⟶ blowup I := blowupChartι I i.1 i.2
  have hcover (x : blowup I) : ∃ (i : ι) (t : Spec (B i)), g i t = x := by
    obtain ⟨U, y, hy⟩ := exists_blowupAffineι I x
    let 𝒱 := affineBlowupChartCover (I.ideal U)
    obtain ⟨t, ht⟩ := 𝒱.covers y
    change affineBlowupChartι (I.ideal U) (𝒱.idx y) t = y at ht
    exact ⟨⟨U, 𝒱.idx y⟩, t, (congrArg (blowupAffineι I U) ht).trans hy⟩
  let V (i : ι) : Set (blowup I) := Set.range (g i)
  have hv : (Set.univ : Set (blowup I)) ⊆ ⋃ i, V i := fun x _ =>
    Set.mem_iUnion.mpr (hcover x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V
    (fun i => IsOpenImmersion.isOpen_range (g i)) hv
  have hc (x : blowup I) : ∃ i : s, x ∈ Set.range (g i.1) := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨his, ht⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, his⟩, ht⟩
  let 𝒰 : (blowup I).AffineOpenCover :=
    { I₀ := s
      X i := B i.1
      f i := g i.1
      idx x := (hc x).choose
      covers x := (hc x).choose_spec }
  refine ⟨𝒰, inferInstanceAs (Finite s), fun j => ?_⟩
  let U := j.1.1
  let c := j.1.2
  let φ := chartBaseMap (I.ideal U) c
  let a := φ c.1
  let : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian U
  refine ⟨blowupChartRing_isNoetherianRing (I.ideal U) c, a,
    isRegular_iff_mem_nonZeroDivisors.mpr (chartBaseMap_mem_nonZeroDivisors (I.ideal U) c), ?_⟩
  change blowupChartι I U c ⁻¹ᵁ blowupπ I ⁻¹ᵁ centerComplement I = _
  rw [← Scheme.Hom.comp_preimage, blowupChartι_π, affine_preimage_centerComplement,
    specIdealEquiv_comap_affine_local]
  change affineCenterComplement ((I.ideal U).map φ) = PrimeSpectrum.basicOpen a
  rw [show (I.ideal U).map φ = Ideal.span {a} from chart_map_ideal_eq_span (I.ideal U) c,
    affineCenterComplement_span_singleton]

end SerrePositivity.AlgebraicGeometry
