module

public import SerrePositivity.AlgebraicGeometry.BlowupChartIdeals
public import SerrePositivity.AlgebraicGeometry.EtaleCenterSourceFlatness
public import SerrePositivity.AlgebraicGeometry.EtaleCommonCenterPullbacks
public import SerrePositivity.AlgebraicGeometry.FiniteTypePureTransformFlatSpec
public import SerrePositivity.AlgebraicGeometry.IdealFlattening
public import SerrePositivity.AlgebraicGeometry.PureTransformTensorSourceCover
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseChangeFlat

/-!
概要：étale 局所の有限個の中心から、元のアフィン基底上の平坦化中心を作る。
方針：共通のブローアップ上で局所中心の平坦性を試験環へ運び、始域の有限被覆で降下する。
規約：境界は正則な一元で表す。
使われ方：Stacks 0814 をファイバー台の次元帰納の各段に適用する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- 全標準チャートで係数写像と二通りの純変換を比較する。
/--
概要：有限型アフィン始域を覆う有限な étale 族の局所中心があれば、元の基底に平坦化中心が存在する。
方針：局所中心を因子に含む共通中心を取り、各標準チャートで始域の平坦被覆から純変換の平坦性を降下する。
規約：各局所基底は étale で、局所中心は境界元の冪を含む。
使われ方：次元を制御した相対 Noether 正規化の局所中心を、元のアフィン基底へ降ろす。
-/
theorem exists_affine_flatPure_center_of_etale_source_centers
    {R : CommRingCat.{u}} {B M ι : Type u} [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Finite ι]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (C D : ι → Type u) [∀ i, CommRing (C i)] [∀ i, CommRing (D i)]
    [∀ i, Algebra R (C i)] [∀ i, Algebra R (D i)] [∀ i, Algebra (C i) (D i)]
    [∀ i, Algebra B (D i)] [∀ i, IsScalarTower R (C i) (D i)]
    [∀ i, IsScalarTower R B (D i)] [∀ i, Algebra.Etale R (C i)] [∀ i, Module.Flat B (D i)]
    (hcover : ∀ q : PrimeSpectrum B, ∃ (i : ι) (t : PrimeSpectrum (D i)),
      t.comap (algebraMap B (D i)) = q)
    (a : R) (ha : IsRegular a) (J : ∀ i, Ideal (C i))
    (hJ : ∀ i, ∃ k : ℕ, algebraMap R (C i) (a ^ k) ∈ J i)
    (hflat : ∀ i, HasFlatPurePullbacks (affineBlowupπ (J i)) (algebraMap R (C i) a) (D i ⊗[B] M)) :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement I ∧
      HasFlatPurePullbacks (affineBlowupπ I) a M := by
  let N (i : ι) := D i ⊗[B] M
  obtain ⟨I, hI, ⟨n, hn⟩, hflat'⟩ :=
    exists_common_affineBlowup_of_etale_flatPure_centers C J a N hJ hflat
  refine ⟨I, hI, basicOpen_le_affineCenterComplement_of_pow_mem I a n hn, ?_⟩
  let p := affineBlowupπ I
  apply hasFlatPurePullbacks_of_openCover p a M (affineBlowupChartCover I).openCover
  intro b
  let A := CommRingCat.of (BlowupChartRing I b)
  let j := affineBlowupChartι I b
  let φ := chartBaseMap I b
  have hj : j ≫ p = Spec.map (CommRingCat.ofHom φ) := affineBlowupChartIso_inv_ι_π I b
  change HasFlatPurePullbacks (j ≫ p) a M
  rw [hj]
  let : IsNoetherianRing A := blowupChartRing_isNoetherianRing I b
  apply hasFlatPurePullbacks_spec_of_finiteTypeModule B (CommRingCat.ofHom φ) a M
  let P (ψ : R →+* A) : Prop :=
    letI : Algebra R A := ψ.toAlgebra
    IsRegular (ψ a) → Module.Flat A (modulePureTransform (ψ a) (A ⊗[R] M))
  have hmap : pureTransformCoefficientMap p j = φ := by
    unfold pureTransformCoefficientMap
    rw [hj, Spec.preimage_map]
    rfl
  have htest : P (pureTransformCoefficientMap p j) := by
    let ψ := pureTransformCoefficientMap p j
    let : Algebra R A := ψ.toAlgebra
    intro hreg
    let E := A ⊗[R] B
    let : Algebra B E := Algebra.TensorProduct.rightAlgebra
    let T := E ⊗[B] M
    let : Module.Flat A (modulePureTransform (algebraMap A E (ψ a)) T) :=
      modulePureTransform_flat_of_tensorSourceCover D hcover (ψ a) (fun i =>
        (hflat' i).flat_source_affine_test p j (C i) (D i) a (N i) hreg)
    let e₁ := modulePureTransformScalarRestrictionEquiv (B := E) (M := T) (ψ a)
    let e₂ := modulePureTransformCongr (ψ a) (tensorAlgebraBaseChangeEquiv R B A M)
    exact Module.Flat.of_linearEquiv (e₂.symm.trans e₁)
  exact (congrArg P hmap).mp htest (isRegular_iff_mem_nonZeroDivisors.mpr
    (chartBaseMap_nonZeroDivisors I b ha.mem_nonZeroDivisors))

end SerrePositivity.AlgebraicGeometry
