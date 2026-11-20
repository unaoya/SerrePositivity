module

public import SerrePositivity.KST.Descent.StrictTransformOpenCharts
public import SerrePositivity.KST.Descent.OpenImageAmbientIso

/-!
# strict transform チャートの任意の実際の Cartesian モデル

## 概要
周辺チャートを表す具体的な Cartesian モデルから、開部分の像と平坦性を移す。

## 方針
同じ実際の引き戻しを表す標準同型を使い、境界とチャート基底への構造射を保持する。

## 規約
Cartesian 性と境界の等式は実際の射・開集合で検査する。降下の結論をフィールドに含めない。

## 使われ方
論文 補題 3.3、公理 (6) の全切断環の Spec と元のアフィンスキームの比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable {X Y C M : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (J : Y.IdealSheafData)
  (j : C ⟶ _root_.SerrePositivity.AlgebraicGeometry.blowup J)

/-- 概要：実際の周辺チャートは元の射とチャート構造射の合成の引き戻し（補題 3.3）。
方針：二つの選択された Cartesian 正方形を縦に貼り合わせる。
規約：元のスキームが特定の環の Spec に定義上等しいとは要求しない。
使われ方：全切断環からの具体的モデルとの比較。 -/
theorem strictTransformChartAmbient_isPullback :
    IsPullback (pullback.fst (pullback.snd f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫ pullback.fst f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J))
      (pullback.snd (pullback.snd f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j) f (j ≫ _root_.SerrePositivity.AlgebraicGeometry.blowupπ J) :=
  ((IsPullback.of_hasPullback (pullback.snd f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j).flip.paste_vert
    (IsPullback.of_hasPullback f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)).flip).flip

variable (a : M ⟶ X) (b : M ⟶ C) (hmodel : IsPullback a b f (j ≫ _root_.SerrePositivity.AlgebraicGeometry.blowupπ J))

/-- 概要：具体的な Cartesian モデルと実際の周辺チャートの標準同型（論文 補題 3.3）。
方針：両者の同じ引き戻しへの標準同型を合成する。
規約：引き戻しの選択や型クラスを変更しない。
使われ方：同型で表示したアフィンスキームとテンソル積のモデルの接続。 -/
noncomputable def strictTransformChartModelIso : M ≅ strictTransformChartAmbient f J j :=
  hmodel.isoPullback ≪≫ (strictTransformChartAmbient_isPullback f J j).isoPullback.symm

/-- 概要：周辺チャートのモデル同型はチャート基底への射を保つ（論文 補題 3.3）。
方針：二つの標準同型の第二射影公式を合成する。
規約：指定した b そのものとの等式。
使われ方：基底を固定した平坦性の移送。 -/
theorem strictTransformChartModelIso_hom_snd :
    (strictTransformChartModelIso f J j a b hmodel).hom ≫
      pullback.snd (pullback.snd f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j = b :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (strictTransformChartAmbient_isPullback f J j).isoPullback_inv_snd).trans
      hmodel.isoPullback_hom_snd)

/-- 概要：周辺チャートのモデル同型は元の始域への射を保つ（論文 補題 3.3）。
方針：二つの標準同型の第一射影公式を合成する。
規約：元の X とその全切断環の Spec の間の射を消去しない。
使われ方：元の境界開部分のモデル側での逆像。 -/
theorem strictTransformChartModelIso_hom_fst_fst :
    (strictTransformChartModelIso f J j a b hmodel).hom ≫
      (pullback.fst (pullback.snd f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫ pullback.fst f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) = a :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (strictTransformChartAmbient_isPullback f J j).isoPullback_inv_fst).trans
      hmodel.isoPullback_hom_fst)

/-- 概要：モデル同型は元の基底の開集合の逆像を保つ（論文 補題 3.3）。
方針：元の始域への指定射の保存に、基底への射を合成して開集合を引き戻す。
規約：開部分は元の strict transform を定義した同じ U。
使われ方：全切断環の境界基本開との比較。 -/
theorem strictTransformChartModelIso_preimage :
    (strictTransformChartModelIso f J j a b hmodel).hom ⁻¹ᵁ
      strictTransformChartOpen f U J j = (a ≫ f) ⁻¹ᵁ U := by
  have hbase : (strictTransformChartModelIso f J j a b hmodel).hom ≫
      (pullback.fst (pullback.snd f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫ (pullback.fst f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J) ≫ f)) =
        a ≫ f :=
    (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (strictTransformChartModelIso_hom_fst_fst f J j a b hmodel)))
  have he := congrArg (fun k : M ⟶ Y ↦ k ⁻¹ᵁ U) hbase
  have hl : ((strictTransformChartModelIso f J j a b hmodel).hom ≫
      (pullback.fst (pullback.snd f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j ≫ (pullback.fst f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J) ≫ f))) ⁻¹ᵁ U =
      (strictTransformChartModelIso f J j a b hmodel).hom ⁻¹ᵁ
        strictTransformChartOpen f U J j :=
    (Scheme.Hom.comp_preimage _ _ _).trans
      (congrArg (fun W ↦ (strictTransformChartModelIso f J j a b hmodel).hom ⁻¹ᵁ W)
        (Scheme.Hom.comp_preimage _ _ _))
  exact hl.symm.trans he

variable [QuasiCompact (_root_.SerrePositivity.AlgebraicGeometry.strictTransformOpen f U J).ι]

set_option backward.isDefEq.respectTransparency false in
/-- 概要：元の開包含の準コンパクト性は任意の周辺チャートでも保たれる（論文 補題 3.3）。
方針：実際の開部分の Cartesian 正方形で準コンパクト性を底変換する。
規約：チャート環や定義上の Spec 表示を要求しない。
使われ方：周辺チャートと具体的モデルの像の比較。 -/
theorem strictTransformChartOpen_quasiCompact_of_source :
    QuasiCompact (strictTransformChartOpen f U J j).ι :=
  MorphismProperty.of_isPullback
    (isPullback_morphismRestrict (pullback.fst (pullback.snd f (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J)) j)
      (_root_.SerrePositivity.AlgebraicGeometry.strictTransformOpen f U J)) inferInstance

/-- 概要：Cartesian モデルの境界の像と実際の周辺チャートの境界の像の同型（補題 3.3）。
方針：周辺同型と同じ境界開部分の保存で、構造層を持つ実際の像を移す。
規約：モデル側の開部分は (a≫f) の U の逆像。
使われ方：全切断環のモデルでの平坦性の移送。 -/
noncomputable def strictTransformChartModelImageIso :
    ((a ≫ f) ⁻¹ᵁ U).ι.image ≅ (strictTransformChartOpen f U J j).ι.image := by
  have := strictTransformChartOpen_quasiCompact_of_source f U J j
  exact openImageAmbientIsoOfEq (strictTransformChartModelIso f J j a b hmodel) _ _
    (strictTransformChartModelIso_preimage f U J j a b hmodel)

/-- 概要：モデルの像の同型は実際の周辺空間への射を保つ（論文 補題 3.3）。
方針：周辺同型による像の移送の閉包含の公式を使う。
規約：元のモデル同型の hom を右辺に保持する。
使われ方：チャート基底への構造射の検査。 -/
theorem strictTransformChartModelImageIso_hom_imageι :
    (strictTransformChartModelImageIso f U J j a b hmodel).hom ≫
      (strictTransformChartOpen f U J j).ι.imageι =
        ((a ≫ f) ⁻¹ᵁ U).ι.imageι ≫ (strictTransformChartModelIso f J j a b hmodel).hom := by
  have := strictTransformChartOpen_quasiCompact_of_source f U J j
  exact openImageAmbientIsoOfEq_hom_imageι (strictTransformChartModelIso f J j a b hmodel)
    (strictTransformChartOpen f U J j) ((a ≫ f) ⁻¹ᵁ U)
    (strictTransformChartModelIso_preimage f U J j a b hmodel)

variable [IsOpenImmersion j]

/-- 概要：モデルの実際の像と元の strict transform のチャートの基底上の同型（補題 3.3）。
方針：周辺チャートの像との同型を global な構造射の底変換との同型に合成する。
規約：元の f・J・j を変更しない。
使われ方：元のアフィンスキームを全切断環で表示した局所計算の接続。 -/
noncomputable def strictTransformChartModelPullbackIso :
    ((a ≫ f) ⁻¹ᵁ U).ι.image ≅ pullback (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f U J) j :=
  strictTransformChartModelImageIso f U J j a b hmodel ≪≫ strictTransformOpenChartIso f U J j

/-- 概要：モデルの像と元のチャートの同型は指定した基底への射 b を保つ（補題 3.3）。
方針：像の二つの同型の因子化とモデルの第二射影の保存を合成する。
規約：実際のスキームの構造射の等式。
使われ方：平坦性をチャート基底上で移す。 -/
theorem strictTransformChartModelPullbackIso_hom_snd :
    (strictTransformChartModelPullbackIso f U J j a b hmodel).hom ≫
      pullback.snd (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f U J) j = ((a ≫ f) ⁻¹ᵁ U).ι.imageι ≫ b :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (strictTransformOpenChartIso_hom_snd f U J j)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (strictTransformChartModelImageIso_hom_imageι f U J j a b hmodel)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (_ ≫ ·) (strictTransformChartModelIso_hom_snd f J j a b hmodel))))))

include hmodel in
/-- 概要：具体的な Cartesian モデルの境界の像が平坦なら元の strict transform のチャートも平坦（補題 3.3）。
方針：実際の像の基底上の同型の逆射で平坦性を移す。
規約：モデルは実際の Cartesian 性を満たす必要がある。
使われ方：全切断環のテンソル積による平坦化を元のスキーム射へ渡す。 -/
theorem strictTransform_chart_flat_of_modelImage
    (hflat : Flat (((a ≫ f) ⁻¹ᵁ U).ι.imageι ≫ b)) :
    Flat (pullback.snd (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f U J) j) := by
  let e := strictTransformChartModelPullbackIso f U J j a b hmodel
  have h : e.inv ≫ (((a ≫ f) ⁻¹ᵁ U).ι.imageι ≫ b) =
      pullback.snd (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f U J) j :=
    e.inv_comp_eq.mpr (strictTransformChartModelPullbackIso_hom_snd f U J j a b hmodel).symm
  have : Flat (e.inv ≫ (((a ≫ f) ⁻¹ᵁ U).ι.imageι ≫ b)) := inferInstance
  exact h ▸ this

end SerrePositivity.KST.Descent
