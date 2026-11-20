module

public import SerrePositivity.KST.Descent.StrictTransformChartModel
public import SerrePositivity.KST.Descent.AffineTensorSquare
public import SerrePositivity.KST.Descent.AffineOpenPureTransform

/-!
# 元のアフィンスキームの同型表示を保持したテンソル積チャート

## 概要
元のスキームを全切断環の Spec と同型で表示し、その同型を消去せずにチャートの平坦性を得る。

## 方針
テンソル積の Cartesian 正方形を両端の実際の同型で移し、境界の逆像を検査する。

## 規約
元のスキームとその全切断環の Spec は定義上同一とは扱わない。

## 使われ方
論文 補題 3.3、公理 (6) の実際の標準 blowup チャート全体への適用。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (eX : Spec (.of B) ≅ X) (eY : Spec (.of R) ≅ Y)
  (hf : eX.hom ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ eY.hom)
  (J : Y.IdealSheafData) (j : Spec (.of C) ⟶ _root_.SerrePositivity.AlgebraicGeometry.blowup J)
  (hj : j ≫ _root_.SerrePositivity.AlgebraicGeometry.blowupπ J = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ eY.hom)

include hf hj in
/-- 概要：両端のアフィン同型を保ったテンソル積の Spec は実際の底変換を表す（補題 3.3）。
方針：指定二射影の Cartesian 正方形を元の始域・基底への同型で移す。
規約：eX・eY と二つの指定可換式を保持する。
使われ方：元の strict transform の周辺チャートの具体的な Cartesian モデル。 -/
theorem affineTensorChartModel_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] C ⊗[R] B).toRingHom) ≫ eX.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B)))) f (j ≫ _root_.SerrePositivity.AlgebraicGeometry.blowupπ J) := by
  apply (tensorSpecSquare_isPullback R C B).flip.of_iso
    (Iso.refl _) eX (Iso.refl _) eY
  · exact (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact hf.symm
  · exact hj.symm.trans (Category.id_comp _).symm

include hf in
/-- 概要：元の基底の境界開部分とテンソル積の係数基本開が対応する（論文 補題 3.3）。
方針：元の射のアフィン同型との可換性とテンソル積の二射影の可換性を合成する。
規約：境界 U は eY の hom の逆像が同じ D(r) になる開集合。
使われ方：全切断環で定義した境界の像を元のスキームへ移す。 -/
theorem affineTensorChartModel_boundary (U : Y.Opens) (r : R)
    (hU : eY.hom ⁻¹ᵁ U = PrimeSpectrum.basicOpen r) :
    ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      B →ₐ[R] C ⊗[R] B).toRingHom) ≫ eX.hom) ≫ f) ⁻¹ᵁ U =
        algebraBoundaryOpen C (C ⊗[R] B) (algebraMap R C r) := by
  have hbase :
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] C ⊗[R] B).toRingHom) ≫ eX.hom) ≫ f =
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R C))) ≫ eY.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) hf).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ eY.hom) (tensorSpecSquare_comm R C B).symm)))
  have he := congrArg (fun k : Spec (.of (C ⊗[R] B)) ⟶ Y ↦ k ⁻¹ᵁ U) hbase
  have hr :
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R C))) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens) =
      algebraBoundaryOpen C (C ⊗[R] B) (algebraMap R C r) := by
    ext x
    rfl
  exact he.trans ((Scheme.Hom.comp_preimage _ _ _).trans
    ((congrArg (fun W ↦ (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R C))) ⁻¹ᵁ W) hU).trans hr))

include hf hj in
/-- 概要：全切断環の同型表示での純変換の平坦性から元の strict transform のチャートの平坦性（補題 3.3）。
方針：両端の同型を保つ実際の Cartesian モデルと境界の像の一致を一般的なチャート比較へ渡す。
規約：元の X・Y とその Spec 表示の同型・可換式を全て明示する。
使われ方：実際の標準チャートの係数写像の公式をそのまま適用する。 -/
theorem strictTransform_chart_flat_of_affineModel (U : Y.Opens) (r : R)
    (hU : eY.hom ⁻¹ᵁ U = PrimeSpectrum.basicOpen r)
    [QuasiCompact (_root_.SerrePositivity.AlgebraicGeometry.strictTransformOpen f U J).ι] [IsOpenImmersion j]
    [Module.Flat C (_root_.SerrePositivity.AlgebraicGeometry.modulePureTransform (algebraMap R C r) (C ⊗[R] B))] :
    Flat (pullback.snd (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f U J) j) := by
  apply strictTransform_chart_flat_of_modelImage f U J j _ _
    (affineTensorChartModel_isPullback R B C f eX eY hf J j hj)
  have he := affineTensorChartModel_boundary R B C f eX eY hf U r hU
  have hEq := congrArg (fun W : (Spec (.of (C ⊗[R] B))).Opens ↦
    Flat (W.ι.imageι ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))))) he
  exact Eq.mpr hEq (algebraBoundaryOpen_image_flat C (C ⊗[R] B) (algebraMap R C r))

end SerrePositivity.KST.Descent
