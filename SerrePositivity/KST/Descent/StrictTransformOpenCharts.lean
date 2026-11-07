module

public import SerrePositivity.KST.Descent.ImageOpenBaseChange
public import SerrePositivity.AlgebraicGeometry.StrictTransform
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# global strict transform の開チャートのスキーム論的像による表示

## 概要
blowup の開チャート上の strict transform を、周辺空間の対応する開部分の実際の像で記述する。

## 方針
像と開底変換の両立を使い、二段の引き戻しを貼り合わせる。

## 規約
チャート上の構造射を保つ。アフィンテンソル積モデルとの同定は別工程。

## 使われ方
論文 補題 3.3、公理 (6) の実際の平坦化を開被覆上で貼り合わせる入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SerrePositivity.AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (J : S.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/-- 概要：局所 Noether 基底の有限型射では strict transform を定義する開包含は準コンパクト（補題 3.3）。
方針：blowup と周辺ファイバー積の局所 Noether 性から開埋め込みの準コンパクト性を得る。
規約：平坦化や像の底変換の結論を仮定しない。
使われ方：スキーム論的像と開底変換の両立の入力。 -/
instance strictTransformOpen_quasiCompact [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    QuasiCompact (strictTransformOpen f U J).ι := by
  have : IsLocallyNoetherian (blowup J) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowupπ J)
  have : IsLocallyNoetherian (strictTransformAmbient f J) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (blowupπ J))
  infer_instance

variable {C : Scheme.{u}} (j : C ⟶ blowup J)

/-- 概要：blowup のチャートで底変換した実際の周辺空間（論文 補題 3.3）。
方針：元の周辺ファイバー積の基底への射をチャートで引き戻す。
規約：既存の選択された引き戻しを使う。
使われ方：チャート上で閉包を取る周辺空間。 -/
noncomputable abbrev strictTransformChartAmbient : Scheme.{u} :=
  pullback (pullback.snd f (blowupπ J)) j

/-- 概要：周辺チャートの境界外の開部分（論文 補題 3.3）。
方針：元の strict transform を定義した開部分を実際の第一射影で引き戻す。
規約：ここではアフィン環の基本開との一致をまだ要求しない。
使われ方：そのスキーム論的像をチャート上の strict transform に同定する。 -/
noncomputable def strictTransformChartOpen : (strictTransformChartAmbient f J j).Opens :=
  pullback.fst (pullback.snd f (blowupπ J)) j ⁻¹ᵁ strictTransformOpen f U J

/-- 概要：二段の周辺引き戻しは strict transform 構造射の底変換と Cartesian（補題 3.3）。
方針：閉包含の引き戻しと周辺空間の引き戻しの二正方形を貼り合わせる。
規約：基底の構造射は定義済みの実際の strictTransformπ。
使われ方：チャート上の構造射を保つ標準同型。 -/
theorem strictTransformChartPullback_isPullback :
    IsPullback
      (pullback.fst (strictTransformι f U J)
        (pullback.fst (pullback.snd f (blowupπ J)) j))
      (pullback.snd (strictTransformι f U J)
        (pullback.fst (pullback.snd f (blowupπ J)) j) ≫
          pullback.snd (pullback.snd f (blowupπ J)) j)
      (strictTransformπ f U J) j :=
  ((IsPullback.of_hasPullback (strictTransformι f U J)
    (pullback.fst (pullback.snd f (blowupπ J)) j)).flip.paste_horiz
      (IsPullback.of_hasPullback (pullback.snd f (blowupπ J)) j).flip).flip

/-- 概要：二段の周辺引き戻しと strict transform 構造射の底変換の標準同型（補題 3.3）。
方針：貼り合わせた実際の Cartesian 正方形の普遍性を使う。
規約：型クラスの別の引き戻しの選択には変更しない。
使われ方：開チャート上の像から元の構造射のチャートへの比較。 -/
noncomputable def strictTransformChartPullbackIso :
    pullback (strictTransformι f U J) (pullback.fst (pullback.snd f (blowupπ J)) j) ≅
      pullback (strictTransformπ f U J) j :=
  (strictTransformChartPullback_isPullback f U J j).isoPullback

/-- 概要：二段の引き戻しの同型はチャート基底への射を保つ（論文 補題 3.3）。
方針：Cartesian 正方形の標準同型の第二射影公式を使う。
規約：チャート C への実際の射。
使われ方：平坦性をチャートの構造射へ移す。 -/
theorem strictTransformChartPullbackIso_hom_snd :
    (strictTransformChartPullbackIso f U J j).hom ≫ pullback.snd (strictTransformπ f U J) j =
      pullback.snd (strictTransformι f U J)
        (pullback.fst (pullback.snd f (blowupπ J)) j) ≫
          pullback.snd (pullback.snd f (blowupπ J)) j :=
  (strictTransformChartPullback_isPullback f U J j).isoPullback_hom_snd

variable [QuasiCompact (strictTransformOpen f U J).ι] [IsOpenImmersion j]

set_option backward.isDefEq.respectTransparency false in
/-- 概要：周辺チャートの開部分の像は global strict transform の実際のチャートと同型（補題 3.3）。
方針：像と開底変換の標準同型、二射影の交換、二段引き戻しの貼り合わせを合成する。
規約：global strict transform の基底変更を実際の像として同定する。
使われ方：アフィンチャートの像で証明した平坦性を global な構造射へ渡す。 -/
noncomputable def strictTransformOpenChartIso :
    (strictTransformChartOpen f U J j).ι.image ≅ pullback (strictTransformπ f U J) j :=
  imageOpenBaseChangeIsoOfIsPullback (strictTransformOpen f U J).ι
    (pullback.fst (pullback.snd f (blowupπ J)) j)
    (strictTransformChartOpen f U J j).ι
    (pullback.fst (pullback.snd f (blowupπ J)) j ∣_ strictTransformOpen f U J)
    (isPullback_morphismRestrict _ _).flip ≪≫
      pullbackSymmetry _ _ ≪≫ strictTransformChartPullbackIso f U J j

set_option backward.isDefEq.respectTransparency false in
/-- 概要：strict transform の開チャートの同型はチャートへの構造射を保つ（論文 補題 3.3）。
方針：三つの同型の第二射影公式と閉包含の保存を合成する。
規約：像から周辺チャートの第二射影への指定合成と一致する。
使われ方：開被覆上の実際の平坦性の貼り合わせ。 -/
theorem strictTransformOpenChartIso_hom_snd :
    (strictTransformOpenChartIso f U J j).hom ≫ pullback.snd (strictTransformπ f U J) j =
      (strictTransformChartOpen f U J j).ι.imageι ≫
        pullback.snd (pullback.snd f (blowupπ J)) j := by
  let e₁ := imageOpenBaseChangeIsoOfIsPullback (strictTransformOpen f U J).ι
    (pullback.fst (pullback.snd f (blowupπ J)) j)
    (strictTransformChartOpen f U J j).ι
    (pullback.fst (pullback.snd f (blowupπ J)) j ∣_ strictTransformOpen f U J)
    (isPullback_morphismRestrict _ _).flip
  let e₂ := pullbackSymmetry (pullback.fst (pullback.snd f (blowupπ J)) j)
    (strictTransformι f U J)
  let e₃ := strictTransformChartPullbackIso f U J j
  have h₁ : e₁.hom ≫ pullback.fst (pullback.fst (pullback.snd f (blowupπ J)) j)
      (strictTransformι f U J) = (strictTransformChartOpen f U J j).ι.imageι :=
    imageOpenBaseChangeIsoOfIsPullback_hom_fst _ _ _ _ _
  have h₂ : e₂.hom ≫ pullback.snd (strictTransformι f U J)
      (pullback.fst (pullback.snd f (blowupπ J)) j) =
      pullback.fst (pullback.fst (pullback.snd f (blowupπ J)) j) (strictTransformι f U J) :=
    pullbackSymmetry_hom_comp_snd _ _
  have h₂₃ : (e₂.hom ≫ e₃.hom) ≫ pullback.snd (strictTransformπ f U J) j =
      pullback.fst (pullback.fst (pullback.snd f (blowupπ J)) j) (strictTransformι f U J) ≫
        pullback.snd (pullback.snd f (blowupπ J)) j :=
    (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (strictTransformChartPullbackIso_hom_snd f U J j)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h₂)))
  exact (Category.assoc _ _ _).trans
    ((congrArg (e₁.hom ≫ ·) h₂₃).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h₁)))

/-- 概要：チャート周辺の開部分の像が平坦なら元の strict transform のチャートも平坦（補題 3.3）。
方針：構造射を保つ標準同型の逆射を使って平坦性を移す。
規約：像の平坦性は実際のスキーム射についての条件。
使われ方：アフィンの純変換による局所計算を元の strict transform へ渡す。 -/
theorem strictTransform_chart_flat_of_image_flat
    (hflat : Flat ((strictTransformChartOpen f U J j).ι.imageι ≫
      pullback.snd (pullback.snd f (blowupπ J)) j)) :
    Flat (pullback.snd (strictTransformπ f U J) j) := by
  let e := strictTransformOpenChartIso f U J j
  have h : e.inv ≫ ((strictTransformChartOpen f U J j).ι.imageι ≫
        pullback.snd (pullback.snd f (blowupπ J)) j) =
      pullback.snd (strictTransformπ f U J) j :=
    e.inv_comp_eq.mpr (strictTransformOpenChartIso_hom_snd f U J j).symm
  have : Flat (e.inv ≫ ((strictTransformChartOpen f U J j).ι.imageι ≫
      pullback.snd (pullback.snd f (blowupπ J)) j)) := inferInstance
  exact h ▸ this

/-- 概要：開被覆の全チャートで実際の像が平坦なら global strict transform は平坦（補題 3.3）。
方針：像によるチャート比較で平坦性を移し、平坦性の標的上の Zariski 局所性を使う。
規約：実際の blowup の開被覆を要求する。チャートのアフィンモデルの同定は別工程。
使われ方：加群平坦化の局所的な結論を global な平坦構造射へ貼り合わせる終端。 -/
theorem strictTransform_flat_of_openChart_images
    (𝒰 : (blowup J).OpenCover)
    (hflat : ∀ i, Flat ((strictTransformChartOpen f U J (𝒰.f i)).ι.imageι ≫
      pullback.snd (pullback.snd f (blowupπ J)) (𝒰.f i))) :
    Flat (strictTransformπ f U J) := by
  have : IsZariskiLocalAtTarget @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{u}) (Q := @RingHom.Flat)
  apply IsZariskiLocalAtTarget.of_openCover (P := @Flat) 𝒰
  intro i
  exact strictTransform_chart_flat_of_image_flat f U J (𝒰.f i) (hflat i)

end SerrePositivity.KST.Descent
