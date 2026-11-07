module

public import SerrePositivity.AlgebraicGeometry.AffineFlatPureComposition
public import SerrePositivity.AlgebraicGeometry.FiniteTypePureTransformFlatSpec

/-!
概要：有限型代数上の有限加群について、局所平坦化中心を元のアフィン基底上へ降ろす。
方針：チャートの平坦性を全アフィン引き戻しへ移し、既存の共通細分と二段合成の支配を使う。
規約：局所中心は最初のブローアップの有限生成元チャート上に与える。
使われ方：Stacks 0815 の局所平坦化を一つの中心にまとめる。
-/

@[expose] public noncomputable section

universe u v w z

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限型代数上有限な加群の局所平坦化中心から、全標準チャートで平坦にする一つの中心を得る。
方針：有限型代数上の有限性を使ってチャートの平坦性を任意の正則境界の引き戻しへ移す。
規約：チャート環上の二段のテンソル積は、合成した係数写像での一度の基底変更として入力する。
使われ方：基礎環上の有限性を課さずに、Stacks 0815 の局所中心を大域化する。
-/
theorem exists_affine_finiteType_flatPure_center_of_local_centers
    {R : Type u} [CommRing R] [IsNoetherianRing R] (B : Type z) [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B]
    (I : Ideal R) {ι : Type w} [Finite ι] (C : ι → I)
    (hC : Ideal.span (Set.range (fun i => (C i).val)) = I)
    (f : R) (hf : f ∈ nonZeroDivisors R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (hI : PrimeSpectrum.basicOpen f ≤ affineCenterComplement I)
    (K : ∀ i, Ideal (BlowupChartRing I (C i)))
    (hK : ∀ i, PrimeSpectrum.basicOpen (chartBaseMap I (C i) f) ≤ affineCenterComplement (K i))
    (hflat : ∀ (i) (b : K i),
      let ψ := (chartBaseMap (K i) b).comp (chartBaseMap I (C i))
      letI : Algebra R (BlowupChartRing (K i) b) := ψ.toAlgebra
      Module.Flat (BlowupChartRing (K i) b)
        (modulePureTransform (ψ f) (BlowupChartRing (K i) b ⊗[R] M))) :
    ∃ J : Ideal R, J.FG ∧ PrimeSpectrum.basicOpen f ≤ affineCenterComplement J ∧
      ∀ b : J, letI : Algebra R (BlowupChartRing J b) := (chartBaseMap J b).toAlgebra
        Module.Flat (BlowupChartRing J b)
          (modulePureTransform (chartBaseMap J b f) (BlowupChartRing J b ⊗[R] M)) := by
  let 𝒰 := affineBlowupGeneratorChartCover I C hC
  have : Finite 𝒰.I₀ := by change Finite ι; infer_instance
  let p := affineBlowupπ I
  let U := p ⁻¹ᵁ PrimeSpectrum.basicOpen f
  let L (i : 𝒰.I₀) := (specIdealEquiv (𝒰.X i)).symm (K i)
  have hbase (i : 𝒰.I₀) : 𝒰.f i ≫ p =
      Spec.map (CommRingCat.ofHom (chartBaseMap I (C i))) :=
    affineBlowupChartIso_inv_ι_π I (C i)
  have hL (i : 𝒰.I₀) : IsUAdmissibleCenter (𝒰.f i ⁻¹ᵁ U) (L i) := by
    change 𝒰.f i ⁻¹ᵁ p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ centerComplement (L i)
    rw [← Scheme.Hom.comp_preimage, hbase, SpecMap_preimage_basicOpen,
      centerComplement_specIdealEquiv]
    exact (OrderIso.apply_symm_apply (specIdealEquiv (𝒰.X i)) (K i)).symm ▸ hK i
  have hLflat (i : 𝒰.I₀) : HasFlatPurePullbacks
      (affineBlowupπ (specIdealEquiv (𝒰.X i) (L i)) ≫ 𝒰.f i ≫ p) f M := by
    let P (J : Ideal (𝒰.X i)) : Prop :=
      HasFlatPurePullbacks (affineBlowupπ J ≫ 𝒰.f i ≫ p) f M
    refine (congrArg P ((specIdealEquiv (𝒰.X i)).apply_symm_apply (K i))).mpr ?_
    change HasFlatPurePullbacks (affineBlowupπ (K i) ≫ 𝒰.f i ≫ p) f M
    refine hasFlatPurePullbacks_of_openCover (R := CommRingCat.of R)
      (affineBlowupπ (K i) ≫ 𝒰.f i ≫ p) f M (affineBlowupChartCover (K i)).openCover ?_
    intro b
    change HasFlatPurePullbacks
      (affineBlowupChartι (K i) b ≫ affineBlowupπ (K i) ≫ 𝒰.f i ≫ p) f M
    rw [hbase, ← Category.assoc (affineBlowupChartι (K i) b),
      show affineBlowupChartι (K i) b ≫ affineBlowupπ (K i) =
        Spec.map (CommRingCat.ofHom (chartBaseMap (K i) b)) from
        affineBlowupChartIso_inv_ι_π (K i) b, ← Spec.map_comp]
    let ψ : CommRingCat.of R ⟶ CommRingCat.of (BlowupChartRing (K i) b) :=
      CommRingCat.ofHom ((chartBaseMap (K i) b).comp (chartBaseMap I (C i)))
    have : IsNoetherianRing (BlowupChartRing I (C i)) := blowupChartRing_isNoetherianRing I (C i)
    have : IsNoetherianRing (CommRingCat.of (BlowupChartRing (K i) b)) :=
      blowupChartRing_isNoetherianRing (K i) b
    exact hasFlatPurePullbacks_spec_of_finiteTypeModule B ψ f M (hflat i b)
  obtain ⟨N, hNU, _, hNflat⟩ := exists_admissible_flatPure_refinement p f M U 𝒰 L hL hLflat
  obtain ⟨J, hfg, hU, hJflat⟩ := exists_affine_flatPure_domination I N f M hI hNU.ge hNflat
  exact ⟨J, hfg, hU, fun b => hJflat.affineBlowup_charts hf b⟩

end SerrePositivity.AlgebraicGeometry
