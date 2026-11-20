module

public import SerrePositivity.KST.Descent.StrictTransformTensorChart
public import SerrePositivity.KST.Descent.OpenImageAmbientIso

/-!
# テンソル積の純変換から実際の strict transform チャートへの平坦性の移送

## 概要
テンソル積の基本開の像と global strict transform の実際のチャートを同定する。

## 方針
周辺同型による開部分の像の移送と、global strict transform のチャート表示を合成する。

## 規約
同じ境界元とチャート基底 C への実際の構造射を保持する。

## 使われ方
論文 補題 3.3、公理 (6) の全チャートの加群平坦化を実際のスキームの平坦性へ移す。
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
  (hj : j ≫ _root_.SerrePositivity.AlgebraicGeometry.blowupπ J = Spec.map (CommRingCat.ofHom (algebraMap R C))) (r : R)
  [QuasiCompact (_root_.SerrePositivity.AlgebraicGeometry.strictTransformOpen (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (PrimeSpectrum.basicOpen r) J).ι]

set_option backward.isDefEq.respectTransparency false in
/-- 概要：元の境界開包含が準コンパクトなら周辺チャートの境界開包含も準コンパクト（補題 3.3）。
方針：開部分を表す実際の Cartesian 正方形で準コンパクト性を底変換する。
規約：チャートの Noether 性を新たに要求しない。
使われ方：周辺同型による実際の像の比較の入力を供給する。 -/
instance strictTransformTensorChartOpen_quasiCompact :
    QuasiCompact (strictTransformChartOpen (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (PrimeSpectrum.basicOpen r) J j).ι :=
  MorphismProperty.of_isPullback
    (isPullback_morphismRestrict
      (pullback.fst
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j)
      (_root_.SerrePositivity.AlgebraicGeometry.strictTransformOpen (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (PrimeSpectrum.basicOpen r) J)) inferInstance

/-- 概要：テンソル積の基本開の実際の像と周辺チャートの実際の像の同型（論文 補題 3.3）。
方針：構造射と境界を保つ周辺同型で開部分のスキーム論的像を移す。
規約：同じ境界 D(r) を用いる。
使われ方：加群純変換の平坦性を周辺チャートの像へ移す。 -/
noncomputable def strictTransformTensorImageIso :
    (algebraBoundaryOpen C (C ⊗[R] B) (algebraMap R C r)).ι.image ≅
      (strictTransformChartOpen (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (PrimeSpectrum.basicOpen r) J j).ι.image :=
  openImageAmbientIsoOfEq (strictTransformTensorChartIso R B C J j hj) _ _
    (strictTransformTensorChartIso_preimage_boundary R B C J j hj r)

/-- 概要：テンソル積の像と周辺チャートの像の同型は指定閉包含を保つ（論文 補題 3.3）。
方針：周辺同型による像の移送の因子化公式を適用する。
規約：右辺に元の周辺同型の hom を保持する。
使われ方：基底 C への構造射の可換性。 -/
theorem strictTransformTensorImageIso_hom_imageι :
    (strictTransformTensorImageIso R B C J j hj r).hom ≫
        (strictTransformChartOpen (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (PrimeSpectrum.basicOpen r) J j).ι.imageι =
      (algebraBoundaryOpen C (C ⊗[R] B) (algebraMap R C r)).ι.imageι ≫
        (strictTransformTensorChartIso R B C J j hj).hom :=
  openImageAmbientIsoOfEq_hom_imageι _ _ _ _

variable [IsOpenImmersion j]

/-- 概要：テンソル積の基本開の像と global strict transform の実際のチャートの同型（補題 3.3）。
方針：周辺チャートの像との同型と、global な構造射の底変換との同型を合成する。
規約：チャート j と境界 D(r) を固定する。
使われ方：全 blowup チャートの純変換の平坦化を元の構造射のチャートへ渡す。 -/
noncomputable def strictTransformTensorPullbackIso :
    (algebraBoundaryOpen C (C ⊗[R] B) (algebraMap R C r)).ι.image ≅
      pullback (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (PrimeSpectrum.basicOpen r) J) j :=
  strictTransformTensorImageIso R B C J j hj r ≪≫
    strictTransformOpenChartIso (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (PrimeSpectrum.basicOpen r) J j

/-- 概要：テンソル積の像と strict transform のチャートの同型は基底 C を保つ（補題 3.3）。
方針：二つの像の比較の可換式と周辺同型の C 射影の公式を合成する。
規約：左辺は元の構造射の実際の底変換の第二射影。
使われ方：C 上の加群平坦性を実際のチャートの平坦性へ移す。 -/
theorem strictTransformTensorPullbackIso_hom_snd :
    (strictTransformTensorPullbackIso R B C J j hj r).hom ≫
        pullback.snd (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (PrimeSpectrum.basicOpen r) J) j =
      algebraBoundaryImageπ C (C ⊗[R] B) (algebraMap R C r) :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (strictTransformOpenChartIso_hom_snd
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) (PrimeSpectrum.basicOpen r) J j)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) (strictTransformTensorImageIso_hom_imageι R B C J j hj r)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (_ ≫ ·) (strictTransformTensorChartIso_hom_snd R B C J j hj))))))

include hj in
/-- 概要：チャート係数環上の純変換加群が平坦なら実際の strict transform のチャートも平坦（補題 3.3）。
方針：基本開のスキーム論的像の平坦性を基底を保つ標準同型の逆で移す。
規約：平坦性を調べる基礎環はチャート係数環 C。π_* や通常の点集合に弱めない。
使われ方：実際の全チャートの加群平坦化を global な平坦性の貼り合わせに渡す。 -/
theorem strictTransform_chart_flat_of_tensorPureTransform
    [Module.Flat C (_root_.SerrePositivity.AlgebraicGeometry.modulePureTransform (algebraMap R C r) (C ⊗[R] B))] :
    Flat (pullback.snd (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (PrimeSpectrum.basicOpen r) J) j) := by
  let e := strictTransformTensorPullbackIso R B C J j hj r
  have hp : Flat (algebraBoundaryImageπ C (C ⊗[R] B) (algebraMap R C r)) :=
    algebraBoundaryOpen_image_flat _ _ _
  have h : e.inv ≫ algebraBoundaryImageπ C (C ⊗[R] B) (algebraMap R C r) =
      pullback.snd (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (PrimeSpectrum.basicOpen r) J) j :=
    e.inv_comp_eq.mpr (strictTransformTensorPullbackIso_hom_snd R B C J j hj r).symm
  have : Flat (e.inv ≫ algebraBoundaryImageπ C (C ⊗[R] B) (algebraMap R C r)) := inferInstance
  exact h ▸ this

end SerrePositivity.KST.Descent
