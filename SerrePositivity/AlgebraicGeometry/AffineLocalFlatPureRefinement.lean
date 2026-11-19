module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LocalFlatPureRefinement
public import SerrePositivity.AlgebraicGeometry.BlowupPureTransformPullbacks
public import SerrePositivity.AlgebraicGeometry.PureTransformRestrictBase
public import SerrePositivity.AlgebraicGeometry.AffineBlowupNoetherian
public import SerrePositivity.AlgebraicGeometry.GeneratorChartCover
public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback

/-!
概要：KST §5、Stacks 0815 の最初のアフィン blowup の有限生成元チャート上の平坦化中心をまとめる。
方針：環イデアルを層へ移し、中心の延長と有限共通細分へ平坦性の開局所性を適用する。
規約：最終の中心は最初の blowup 上のイデアル層。
使われ方：二段の admissible blowup の支配で元の基礎環へ平坦化を降ろす。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限生成元チャート上の局所平坦化を最初の blowup 上の一つの admissible 中心でまとめる。
方針：チャート上の中心と平坦性をイデアル層と引き戻しの性質に移し、大域共通細分を構成する。
規約：KST §5、Stacks 0815、二段目の中心の補開集合は最初の構造射による D(f) の逆像。
使われ方：有限加群の実際の大域平坦化中心の構成。
-/
theorem exists_affine_local_flatPure_refinement {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {ι : Type w} [Finite ι] (C : ι → I)
    (hC : Ideal.span (Set.range (fun i => (C i).val)) = I)
    (f : R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (K : ∀ i, Ideal (BlowupChartRing I (C i)))
    (hK : ∀ i, PrimeSpectrum.basicOpen (chartBaseMap I (C i) f) ≤ affineCenterComplement (K i))
    (hflat : ∀ i,
      let A := BlowupChartRing I (C i)
      letI : Algebra R A := (chartBaseMap I (C i)).toAlgebra
      ∀ b : K i, letI : Algebra A (BlowupChartRing (K i) b) := (chartBaseMap (K i) b).toAlgebra
        Module.Flat (BlowupChartRing (K i) b)
          (modulePureTransform (chartBaseMap (K i) b (chartBaseMap I (C i) f))
            (BlowupChartRing (K i) b ⊗[A] (A ⊗[R] M)))) :
    ∃ L : (affineBlowup I).IdealSheafData,
      centerComplement L = affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen f ∧
      (∀ V : (affineBlowup I).affineOpens, (L.ideal V).FG) ∧
      HasFlatPurePullbacks (blowupπ L ≫ affineBlowupπ I) f M := by
  classical
  let 𝒰 := affineBlowupGeneratorChartCover I C hC
  have : Finite 𝒰.I₀ := by change Finite ι; infer_instance
  let U := affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen f
  let L (i : 𝒰.I₀) : (Spec (𝒰.X i)).IdealSheafData := (specIdealEquiv (𝒰.X i)).symm (K i)
  have hL (i : 𝒰.I₀) : IsUAdmissibleCenter (𝒰.f i ⁻¹ᵁ U) (L i) := by
    have hU : 𝒰.f i ⁻¹ᵁ U = PrimeSpectrum.basicOpen (chartBaseMap I (C i) f) := by
      ext x
      change (affineBlowupChartι I (C i) ≫ affineBlowupπ I) x ∈
        PrimeSpectrum.basicOpen f ↔ x ∈ PrimeSpectrum.basicOpen (chartBaseMap I (C i) f)
      rw [show affineBlowupChartι I (C i) ≫ affineBlowupπ I =
        Spec.map (CommRingCat.ofHom (chartBaseMap I (C i))) from
          affineBlowupChartIso_inv_ι_π I (C i)]
      rfl
    change 𝒰.f i ⁻¹ᵁ U ≤ centerComplement (L i)
    rw [hU, centerComplement_specIdealEquiv]
    have he : specIdealEquiv (𝒰.X i) (L i) = K i := (specIdealEquiv (𝒰.X i)).apply_symm_apply _
    rw [he]
    exact hK i
  have hLflat (i : 𝒰.I₀) : HasFlatPurePullbacks
      (affineBlowupπ (specIdealEquiv (𝒰.X i) (L i)) ≫ 𝒰.f i ≫ affineBlowupπ I) f M := by
    change ι at i
    let A := BlowupChartRing I (C i)
    let φ : CommRingCat.of R ⟶ CommRingCat.of A := CommRingCat.ofHom (chartBaseMap I (C i))
    let : Algebra R A := (chartBaseMap I (C i)).toAlgebra
    have : IsNoetherianRing A := blowupChartRing_isNoetherianRing I (C i)
    have hp : HasFlatPurePullbacks (affineBlowupπ (K i)) (chartBaseMap I (C i) f) (A ⊗[R] M) := by
      with_reducible_and_instances
        exact hasFlatPurePullbacks_affineBlowup (K i) (chartBaseMap I (C i) f) (A ⊗[R] M) (hflat i)
    have hp' := HasFlatPurePullbacks.restrictBase φ (affineBlowupπ (K i)) f M hp
    have hebase : 𝒰.f i ≫ affineBlowupπ I = Spec.map φ := affineBlowupChartIso_inv_ι_π I (C i)
    have hp'' : HasFlatPurePullbacks (affineBlowupπ (K i) ≫ 𝒰.f i ≫ affineBlowupπ I) f M := by
      rw [hebase]
      exact hp'
    have he : specIdealEquiv (𝒰.X i) (L i) = K i := (specIdealEquiv (𝒰.X i)).apply_symm_apply _
    let P (J : Ideal (𝒰.X i)) : Prop :=
      HasFlatPurePullbacks (affineBlowupπ J ≫ 𝒰.f i ≫ affineBlowupπ I) f M
    exact (congrArg P he).mpr hp''
  exact exists_admissible_flatPure_refinement (affineBlowupπ I) f M U 𝒰 L hL hLflat

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
