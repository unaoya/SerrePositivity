module

public import SerrePositivity.KST.Descent.StrictTransformOpenCharts
public import SerrePositivity.KST.Descent.AffineOpenPureTransform
public import SerrePositivity.KST.Descent.AffineTensorSquare

/-!
# strict transform の周辺チャートとテンソル積の Spec

## 概要
アフィン射の blowup の実際の周辺チャートをテンソル積の Spec と同定する。

## 方針
実際の Cartesian 正方形と二段の引き戻しの普遍性を使う。

## 規約
チャートの係数射との可換式を明示し、基礎環への構造射と境界基本開を保持する。

## 使われ方
論文 補題 3.3、公理 (6) のアフィン像の平坦化と global strict transform のチャートの接続。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] (J : (Spec (.of R)).IdealSheafData)
  (j : Spec (.of C) ⟶ _root_.SerrePositivity.AlgebraicGeometry.blowup J)
  (hj : j ≫ _root_.SerrePositivity.AlgebraicGeometry.blowupπ J = Spec.map (CommRingCat.ofHom (algebraMap R C)))

include hj in
/-- 概要：テンソル積の Spec は元のアフィン射とチャートの基底への合成の引き戻し（補題 3.3）。
方針：指定二射影の Cartesian 性にチャートの構造射の可換式を適用する。
規約：チャート C をテンソル積の左因子とする。
使われ方：実際の周辺チャートとの標準同型。 -/
theorem strictTransformTensorChart_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] C ⊗[R] B).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) (j ≫ _root_.SerrePositivity.AlgebraicGeometry.blowupπ J) := by
  exact Eq.mpr (congrArg (fun k ↦ IsPullback
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      B →ₐ[R] C ⊗[R] B).toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))))
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) k) hj)
      (tensorSpecSquare_isPullback R C B).flip

omit [Algebra R C] in
/-- 概要：実際の周辺チャートも元の射とチャートの基底への合成の引き戻し（補題 3.3）。
方針：二段の選択された引き戻しの Cartesian 正方形を縦に貼り合わせる。
規約：元の射の周辺空間の選択を変更しない。
使われ方：テンソル積の Spec と同じ引き戻しを表すことの検査。 -/
theorem strictTransformTensorChart_ambient_isPullback :
    IsPullback
      (pullback.fst
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J))
      (pullback.snd
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j)
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) (j ≫ _root_.SerrePositivity.AlgebraicGeometry.blowupπ J) :=
  ((IsPullback.of_hasPullback
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j).flip.paste_vert
      (IsPullback.of_hasPullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)).flip).flip

/-- 概要：テンソル積の Spec と実際の周辺チャートの標準同型（論文 補題 3.3）。
方針：同じ実際の引き戻しを表す二つの Cartesian モデルの標準同型を合成する。
規約：与えられたチャート j と係数射の可換性を使う。
使われ方：アフィン基本開の像を周辺チャートの像へ移す。 -/
noncomputable def strictTransformTensorChartIso :
    Spec (.of (C ⊗[R] B)) ≅
      strictTransformChartAmbient (Spec.map (CommRingCat.ofHom (algebraMap R B))) J j :=
  (strictTransformTensorChart_isPullback R B C J j hj).isoPullback ≪≫
    (strictTransformTensorChart_ambient_isPullback R B C J j).isoPullback.symm

/-- 概要：周辺チャートの標準同型は C への指定射影を保つ（論文 補題 3.3）。
方針：二つの Cartesian モデルの標準同型の第二射影公式を合成する。
規約：左因子 C への射影は実際の代数構造射の Spec。
使われ方：アフィンの平坦性の基底を固定した移送。 -/
theorem strictTransformTensorChartIso_hom_snd :
    (strictTransformTensorChartIso R B C J j hj).hom ≫
        pullback.snd
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j =
      Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))) :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·)
      (strictTransformTensorChart_ambient_isPullback R B C J j).isoPullback_inv_snd).trans
        (strictTransformTensorChart_isPullback R B C J j hj).isoPullback_hom_snd)

/-- 概要：周辺チャートの同型は元の基礎環への構造射も保つ（論文 補題 3.3）。
方針：二つの引き戻しの可換式と C への射影の保存を合成する。
規約：境界基本開の比較に使う実際の構造射の等式。
使われ方：R の境界元と C の像が定める基本開の一致。 -/
theorem strictTransformTensorChartIso_hom_base :
    (strictTransformTensorChartIso R B C J j hj).hom ≫
        (pullback.fst
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫
          (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R B)))) =
      Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  have h₁ :
      pullback.fst
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R B))) =
      pullback.snd
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫
        (j ≫ _root_.SerrePositivity.AlgebraicGeometry.blowupπ J) :=
    (congrArg (_ ≫ ·) (pullback.condition (f :=
      Spec.map (CommRingCat.ofHom (algebraMap R B))) (g := _root_.SerrePositivity.AlgebraicGeometry.blowupπ J))).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) (pullback.condition (f :=
            pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J))
              (g := j))).trans (Category.assoc _ _ _)))
  exact (congrArg (_ ≫ ·) h₁).trans
    ((congrArg (fun k ↦ (strictTransformTensorChartIso R B C J j hj).hom ≫
      (pullback.snd
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫ k)) hj).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (strictTransformTensorChartIso_hom_snd R B C J j hj))))

/-- 概要：周辺チャートの境界開部分はテンソル積の係数の基本開に対応する（補題 3.3）。
方針：基礎環への構造射の等式に基本開の逆像を適用する。
規約：元の D(r) とチャート係数の像による基本開を同じ元で比較する。
使われ方：二つの実際のスキーム論的像の同定。 -/
theorem strictTransformTensorChartIso_preimage_boundary (r : R) :
    (strictTransformTensorChartIso R B C J j hj).hom ⁻¹ᵁ
        strictTransformChartOpen (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (PrimeSpectrum.basicOpen r) J j =
      algebraBoundaryOpen C (C ⊗[R] B) (algebraMap R C r) := by
  have he := congrArg
    (fun k : Spec (.of (C ⊗[R] B)) ⟶ Spec (.of R) ↦
      k ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens))
    (strictTransformTensorChartIso_hom_base R B C J j hj)
  have hleft :
      ((strictTransformTensorChartIso R B C J j hj).hom ≫
        (pullback.fst
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫
          (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R B))))) ⁻¹ᵁ
              (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens) =
      (strictTransformTensorChartIso R B C J j hj).hom ⁻¹ᵁ
        strictTransformChartOpen (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (PrimeSpectrum.basicOpen r) J j :=
    (Scheme.Hom.comp_preimage _ _ _).trans
      (congrArg (fun V ↦ (strictTransformTensorChartIso R B C J j hj).hom ⁻¹ᵁ V)
        (Scheme.Hom.comp_preimage _ _ _))
  have hright :
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R C))) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens) =
      algebraBoundaryOpen C (C ⊗[R] B) (algebraMap R C r) := by
    ext x
    rfl
  exact hleft.symm.trans (he.trans hright)

end SerrePositivity.KST.Descent
