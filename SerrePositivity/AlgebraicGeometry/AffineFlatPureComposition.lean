module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.AffineLocalFlatPureRefinement
public import SerrePositivity.AlgebraicGeometry.AffineAdmissibleComposition

/-!
概要：KST §5、Stacks 0815 の局所平坦化の二段 blowup を元のアフィン基礎環上の中心へ降ろす。
方針：合成を支配する実際の admissible blowup を取り、引き戻しの平坦性を前合成する。
規約：有限加群の平坦性は最後に標準チャート上の実際の平坦性として取り出す。
使われ方：境界外で平坦な有限加群の一つの平坦化中心の構成。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：二段目の blowup 上の引き戻し平坦性を一つのアフィン admissible blowup 上へ移す。
方針：二段合成を支配する実際の射に引き戻し平坦性を前合成する。
規約：KST §5、Stacks 0815、中心が D(f) を避けることを両段で仮定する。
使われ方：局所中心の共通細分を元の基礎環の中心へ降ろす。
-/
theorem exists_affine_flatPure_domination {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (L : (affineBlowup I).IdealSheafData) (f : R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (hI : PrimeSpectrum.basicOpen f ≤ affineCenterComplement I)
    (hL : affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ centerComplement L)
    (hflat : HasFlatPurePullbacks (blowupπ L ≫ affineBlowupπ I) f M) :
    ∃ J : Ideal R, J.FG ∧ PrimeSpectrum.basicOpen f ≤ affineCenterComplement J ∧
      HasFlatPurePullbacks (affineBlowupπ J) f M := by
  obtain ⟨J, hfg, hU, g, hg⟩ := exists_affine_admissible_composition_domination I L
    (PrimeSpectrum.basicOpen f) hI hL
  have heq : g ≫ (blowupπ L ≫ affineBlowupπ I) = affineBlowupπ J := by
    simpa only [Category.assoc] using hg
  exact ⟨J, hfg, hU,
    (congrArg (fun p => HasFlatPurePullbacks p f M) heq).mp (hflat.comp g)⟩

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限生成元チャートの局所平坦化中心から元の基礎環上の一つの実際の平坦化中心を得る。
方針：局所中心を共通細分し、二段合成の支配を取って全標準チャート上の平坦性を取り出す。
規約：KST §5、Stacks 0815、元の境界元は非零因子。
使われ方：Noether 環上有限な加群の平坦化の大域構成。
-/
theorem exists_affine_flatPure_center_of_local_centers
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {ι : Type w} [Finite ι] (C : ι → I)
    (hC : Ideal.span (Set.range (fun i => (C i).val)) = I)
    (f : R) (hf : f ∈ nonZeroDivisors R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : PrimeSpectrum.basicOpen f ≤ affineCenterComplement I)
    (K : ∀ i, Ideal (BlowupChartRing I (C i)))
    (hK : ∀ i, PrimeSpectrum.basicOpen (chartBaseMap I (C i) f) ≤ affineCenterComplement (K i))
    (hflat : ∀ i,
      let A := BlowupChartRing I (C i)
      letI : Algebra R A := (chartBaseMap I (C i)).toAlgebra
      ∀ b : K i, letI : Algebra A (BlowupChartRing (K i) b) := (chartBaseMap (K i) b).toAlgebra
        Module.Flat (BlowupChartRing (K i) b)
          (modulePureTransform (chartBaseMap (K i) b (chartBaseMap I (C i) f))
            (BlowupChartRing (K i) b ⊗[A] (A ⊗[R] M)))) :
    ∃ J : Ideal R, J.FG ∧ PrimeSpectrum.basicOpen f ≤ affineCenterComplement J ∧
      ∀ b : J, letI : Algebra R (BlowupChartRing J b) := (chartBaseMap J b).toAlgebra
        Module.Flat (BlowupChartRing J b)
          (modulePureTransform (chartBaseMap J b f) (BlowupChartRing J b ⊗[R] M)) := by
  obtain ⟨L, hLU, _, hLflat⟩ := exists_affine_local_flatPure_refinement I C hC f M K hK hflat
  obtain ⟨J, hfg, hU, hJflat⟩ := exists_affine_flatPure_domination I L f M hI hLU.ge hLflat
  exact ⟨J, hfg, hU, fun b => hJflat.affineBlowup_charts hf b⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
