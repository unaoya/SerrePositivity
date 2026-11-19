module

public import SerrePositivity.KST.Descent.AffineBlowupFlatness
public import SerrePositivity.KST.Descent.GenericFiniteFlattening

/-!
# 整なアフィン Noether 基底への有限射の実際の平坦化中心

## 概要
有限射の全切断環を用い、境界を避ける実際の中心と平坦な global strict transform を構成する。

## 方針
有限な環準同型の表示から加群平坦化中心を選び、同じ全切断環の全標準チャートで貼り合わせる。

## 規約
平坦化の存在を仮定しない。元のスキームと Spec の同型を明示して保持する。

## 使われ方
論文 補題 3.3、公理 (6) の有限射の場合の実際のアフィン平坦化。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

set_option backward.isDefEq.respectTransparency false in
/-- 概要：整なアフィン Noether 基底への有限射を平坦化する実際の中心が存在（論文 補題 3.3）。
方針：有限な表示環準同型の加群平坦化中心をイデアル層へ移し、実際の全標準チャートで平坦性を貼る。
規約：境界 r は非零で、同じ D(r) を用いた実際の strict transform の構造射が平坦となる。
使われ方：有限全射の場合の全射性・有限忠実平坦細分と、中心上の次元帰納への接続。 -/
theorem exists_affine_finite_flattening_center {X Y : Scheme.{u}} [IsAffine Y]
    [IsNoetherian Y] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f] :
    ∃ (r : Γ(Y, ⊤)) (J : Y.IdealSheafData), r ≠ 0 ∧
      (∀ W : Y.affineOpens, (J.ideal W).FG) ∧ Y.basicOpen r ≤ _root_.SerrePositivity.AlgebraicGeometry.centerComplement J ∧
        J.support ≠ ⊤ ∧ Flat (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f (Y.basicOpen r) J) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let R : Type u := Γ(Y, ⊤)
  let B : Type u := Γ(X, ⊤)
  let eX : Spec (.of B) ≅ X := affineTopPresentation X
  let eY : Spec (.of R) ≅ Y := affineTopPresentation Y
  let φ : R →+* B := affinePresentationMap f eX eY
  let : Algebra R B := φ.toAlgebra
  have : Module.Finite R B := affinePresentationMap_moduleFinite f eX eY
  have hf : eX.hom ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ eY.hom :=
    affinePresentationMap_comm f eX eY
  obtain ⟨r, I, hr, _, hUI, hflatI⟩ := exists_nonzero_finite_module_flattening_center R B
  let J : Y.IdealSheafData := (Scheme.IdealSheafData.equivOfIsAffine (X := Y)).symm I
  have hJ : J.ideal ⟨⊤, isAffineOpen_top Y⟩ = I :=
    (Scheme.IdealSheafData.equivOfIsAffine (X := Y)).apply_symm_apply I
  have hJfg : ∀ W : Y.affineOpens, (J.ideal W).FG := by
    intro W
    have := IsLocallyNoetherian.component_noetherian W
    exact Ideal.fg_of_isNoetherianRing _
  have hpre : eY.hom ⁻¹ᵁ _root_.SerrePositivity.AlgebraicGeometry.centerComplement J = _root_.SerrePositivity.AlgebraicGeometry.affineCenterComplement I :=
    (_root_.SerrePositivity.AlgebraicGeometry.fromSpec_preimage_centerComplement J ⟨⊤, isAffineOpen_top Y⟩).trans
      (congrArg _root_.SerrePositivity.AlgebraicGeometry.affineCenterComplement hJ)
  have hadm : Y.basicOpen r ≤ _root_.SerrePositivity.AlgebraicGeometry.centerComplement J := by
    intro y hy
    obtain ⟨x, rfl⟩ := eY.hom.surjective y
    have hx : x ∈ (PrimeSpectrum.basicOpen r).carrier := by
      change x ∈ eY.hom ⁻¹ᵁ Y.basicOpen r at hy
      rw [show eY.hom ⁻¹ᵁ Y.basicOpen r = PrimeSpectrum.basicOpen r from
        affineTopPresentation_preimage_basicOpen Y r] at hy
      exact hy
    change x ∈ eY.hom ⁻¹ᵁ _root_.SerrePositivity.AlgebraicGeometry.centerComplement J
    rw [hpre]
    exact hUI hx
  let P (K : Ideal R) : Prop :=
    ∀ a : K, letI : Algebra R (_root_.SerrePositivity.AlgebraicGeometry.BlowupChartRing K a) := (_root_.SerrePositivity.AlgebraicGeometry.chartBaseMap K a).toAlgebra
      Module.Flat (_root_.SerrePositivity.AlgebraicGeometry.BlowupChartRing K a)
        (_root_.SerrePositivity.AlgebraicGeometry.modulePureTransform (_root_.SerrePositivity.AlgebraicGeometry.chartBaseMap K a r) (_root_.SerrePositivity.AlgebraicGeometry.BlowupChartRing K a ⊗[R] B))
  have hflatJ : P (J.ideal ⟨⊤, isAffineOpen_top Y⟩) := (congrArg P hJ).mpr hflatI
  have : QuasiCompact (_root_.SerrePositivity.AlgebraicGeometry.strictTransformOpen f (Y.basicOpen r) J).ι := inferInstance
  have hs : Flat (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f (Y.basicOpen r) J) :=
    strictTransform_flat_of_topChart_pureTransforms J f B eX hf r hflatJ
  exact ⟨r, J, hr, hJfg, hadm,
    center_support_ne_top_of_nonzero_boundary Y J r hr hadm, hs⟩

end SerrePositivity.KST.Descent
