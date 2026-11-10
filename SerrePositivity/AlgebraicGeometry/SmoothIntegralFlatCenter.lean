module

public import SerrePositivity.AlgebraicGeometry.BlowupPureTransformPullbacks
public import SerrePositivity.AlgebraicGeometry.FiberFreeOpenCenterGluing
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralFreeOpenBlowup
public import SerrePositivity.AlgebraicGeometry.IteratedFlatCenterGluing
public import SerrePositivity.AlgebraicGeometry.PureTransformBoundaryFlat

/-!
概要：相対次元を指定した滑らかで幾何学的整な族の上で、有限加群を平坦化する。
方針：自由化ブローアップのチャートで余核の次元帰納を使い、二段の中心を一つにする。
規約：正則元で境界の主開を表し、帰納仮定は台の次元が小さい有限加群に対して使う。
使われ方：Stacks 0815 で相対 Noether 正規化先の上に平坦化中心を作る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
-- 二段のブローアップのチャートで係数の代数構造を合成する。
/--
概要：相対次元 n の滑らかで幾何学的整な族の有限加群は、次元 n より小さい台の帰納仮定から平坦化できる。
方針：自由化中心の各チャートで境界外の平坦性を保存し、余核を平坦化して元の中心へ合成する。
規約：有限型の代数上で有限な加群を扱い、基底上の有限性を要求しない。
使われ方：有限な相対 Noether 正規化で押し出した加群に適用する。
-/
theorem exists_affine_flatPure_center_of_smooth_geometricallyIntegral
    {R : CommRingCat.{u}} {B M : Type u} [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Flat R B] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (n : ℕ) [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (a : R) (ha : IsRegular a) [Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] M)]
    (hrec : HasAffineFlatPureCentersBelow.{u} n) :
    ∃ J : Ideal R, J.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement J ∧
      HasFlatPurePullbacks (affineBlowupπ J) a M := by
  classical
  obtain ⟨I, hI, hIU, hfree⟩ :=
    exists_fg_center_boundaryFreeOpenPullbacks_of_geometricallyIntegral B (M := M) a ha
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hI
  let : Finite s := hs.to_subtype
  let c (i : s) : I := ⟨i, hspan ▸ Ideal.subset_span i.2⟩
  have hc : Ideal.span (Set.range (fun i => (c i).val)) = I := by
    rw [show Set.range (fun i => (c i).val) = s from Subtype.range_val]
    exact hspan
  have hloc (i : s) :
      let C := CommRingCat.of (BlowupChartRing I (c i))
      let φ := chartBaseMap I (c i)
      letI : Algebra R C := φ.toAlgebra
      ∃ K : Ideal C, PrimeSpectrum.basicOpen (φ a) ≤ affineCenterComplement K ∧
        HasFlatPurePullbacks (affineBlowupπ K) (φ a) (modulePureTransform (φ a) (C ⊗[R] M)) := by
    let C := CommRingCat.of (BlowupChartRing I (c i))
    let φ := chartBaseMap I (c i)
    let : Algebra R C := φ.toAlgebra
    let : IsNoetherianRing C := blowupChartRing_isNoetherianRing I (c i)
    let D := C ⊗[R] B
    let : Algebra B D := Algebra.TensorProduct.rightAlgebra
    let N := D ⊗[B] M
    let e := φ a
    let G := modulePureTransform (algebraMap C D e) N
    have he : IsRegular e :=
      isRegular_iff_mem_nonZeroDivisors.mpr
        (chartBaseMap_nonZeroDivisors I (c i) ha.mem_nonZeroDivisors)
    have hmap : pureTransformCoefficientMap (affineBlowupπ I) (affineBlowupChartι I (c i)) = φ := by
      unfold pureTransformCoefficientMap
      rw [show affineBlowupChartι I (c i) ≫ affineBlowupπ I =
        Spec.map (CommRingCat.ofHom φ) from affineBlowupChartIso_inv_ι_π I (c i),
        Spec.preimage_map]
      rfl
    let P (ψ : R →+* C) : Prop :=
      letI : Algebra R C := ψ.toAlgebra
      IsRegular (ψ a) → BoundaryPureFreeOpens R B C M (ψ a)
    have hchart : P φ :=
      (congrArg P hmap).mp (hfree C (affineBlowupChartι I (c i)))
    let g := Spec.map (CommRingCat.ofHom (algebraMap C D))
    let : GeometricallyIntegral g := geometricallyIntegral_tensorProjection R B C
    let : SmoothOfRelativeDimension n g :=
      MorphismProperty.of_isPullback (isPullback_specTensor R B C) inferInstance
    let : Module.Flat (Localization.Away e) (Localization.Away e ⊗[C] G) :=
      flat_tensorAlgebra_pureTransform_away_of_boundary_flat (B := B) (C := C) (M := M) a
    have hG (p : PrimeSpectrum C) : ∃ b ∉ p.asIdeal.map (algebraMap C D),
        Module.Free (Localization.Away b) (Localization.Away b ⊗[D] G) := by
      obtain ⟨b, hb, hgb⟩ := hchart he p
      let : Module.Free (Localization.Away b) (LocalizedModule.Away b G) := hgb
      exact ⟨b, hb, Module.Free.of_equiv (LocalizedModule.equivTensorProduct (.powers b) G)⟩
    obtain ⟨K, _, hK, hKflat⟩ := exists_affine_flatPure_center_of_fiber_freeOpens n e he hrec hG
    let E := (modulePureTransformScalarRestrictionEquiv (B := D) (M := N) e).symm.trans
      (modulePureTransformCongr e (tensorAlgebraBaseChangeEquiv R B C M))
    exact ⟨K, hK, hKflat.congrModule E⟩
  choose K hK hKflat using hloc
  obtain ⟨J, hJ, hJU, hJflat⟩ :=
    exists_affine_finiteType_flatPure_center_of_iterated_local_centers B I c hc a
      ha.mem_nonZeroDivisors M hIU.ge K hK (fun i b =>
        (hKflat i).affineBlowup_charts
          (chartBaseMap_nonZeroDivisors I (c i) ha.mem_nonZeroDivisors) b)
  refine ⟨J, hJ, hJU, ?_⟩
  apply hasFlatPurePullbacks_of_openCover (affineBlowupπ J) a M
    (affineBlowupChartCover J).openCover
  intro b
  change HasFlatPurePullbacks (affineBlowupChartι J b ≫ affineBlowupπ J) a M
  rw [show affineBlowupChartι J b ≫ affineBlowupπ J =
    Spec.map (CommRingCat.ofHom (chartBaseMap J b)) from affineBlowupChartIso_inv_ι_π J b]
  let : IsNoetherianRing (CommRingCat.of (BlowupChartRing J b)) :=
    blowupChartRing_isNoetherianRing J b
  exact hasFlatPurePullbacks_spec_of_finiteTypeModule B
    (CommRingCat.ofHom (chartBaseMap J b)) a M (hJflat b)

end SerrePositivity.AlgebraicGeometry
