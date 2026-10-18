module

public import SerrePositivity.KST.Descent.ImageOpenBaseChange

/-!
# 周辺スキームの同型による開部分のスキーム論的像の移送

## 概要
周辺スキームの同型が二つの開部分を対応させるとき、その実際のスキーム論的像も同型になる。

## 方針
像と開底変換の標準同型を使い、同型による引き戻しの第二射影で戻す。

## 規約
同型は元の周辺空間への閉包含と可換する。像を点集合の閉包で代用しない。

## 使われ方
論文 補題 3.3、公理 (6) のテンソル積のアフィン像と実際の周辺チャートの像の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {P Q T : Scheme.{u}}

/-- 概要：同型に沿う実際の引き戻しは第二射影で元の空間と同型（論文 補題 3.3）。
方針：元の空間が同じ引き戻しを表す Cartesian 正方形を作り、標準同型の逆を使う。
規約：選択された引き戻しやその型クラスを変更しない。
使われ方：周辺同型による像の移送。 -/
noncomputable def pullbackLeftIsoSndIso (e : P ≅ Q) (i : T ⟶ Q) :
    pullback e.hom i ≅ T :=
  (IsPullback.of_vert_isIso (show CommSq (i ≫ e.inv) (𝟙 T) e.hom i from
    ⟨by simp⟩)).isoPullback.symm

/-- 概要：同型に沿う引き戻しの同型の hom は実際の第二射影（論文 補題 3.3）。
方針：Cartesian モデルの標準同型の逆射の射影公式を使う。
規約：対象同型の存在だけでなく指定射との一致。
使われ方：像の閉包含の因子化式の保存。 -/
theorem pullbackLeftIsoSndIso_hom (e : P ≅ Q) (i : T ⟶ Q) :
    (pullbackLeftIsoSndIso e i).hom = pullback.snd e.hom i := by
  let h := IsPullback.of_vert_isIso (show CommSq (i ≫ e.inv) (𝟙 T) e.hom i from ⟨by simp⟩)
  exact (Category.comp_id _).symm.trans h.isoPullback_inv_snd

/-- 概要：等しい開部分のスキーム論的像の標準同型（論文 補題 3.3）。
方針：開部分の等式を実際の像の対象へ適用する。
規約：同じ周辺空間の開集合の等式のみを使う。
使われ方：具体的な境界基本開と周辺チャートの逆像開の対応。 -/
noncomputable def openImageCongrIso {V W : P.Opens} (h : V = W) : V.ι.image ≅ W.ι.image :=
  eqToIso (congrArg (fun O : P.Opens ↦ O.ι.image) h)

/-- 概要：等しい開部分の像の同型は指定閉包含を保つ（論文 補題 3.3）。
方針：開集合の等式で場合分けし、恒等同型へ帰着する。
規約：構造射を保持するための等式。
使われ方：周辺同型による像の比較との合成。 -/
theorem openImageCongrIso_hom_imageι {V W : P.Opens} (h : V = W) :
    (openImageCongrIso h).hom ≫ W.ι.imageι = V.ι.imageι := by
  cases h
  exact Category.id_comp _

/-- 概要：周辺同型による開部分の逆像の実際の像は元の像と同型（論文 補題 3.3）。
方針：像の開底変換の同型と、同型に沿う引き戻しの第二射影の同型を合成する。
規約：開包含の準コンパクト性を明示する。
使われ方：テンソル積の像から周辺チャートの像へ移す基本操作。 -/
noncomputable def openImageAmbientIso (e : P ≅ Q) (U : Q.Opens) [QuasiCompact U.ι] :
    (e.hom ⁻¹ᵁ U).ι.image ≅ U.ι.image :=
  imageOpenBaseChangeIsoOfIsPullback U.ι e.hom (e.hom ⁻¹ᵁ U).ι (e.hom ∣_ U)
    (isPullback_morphismRestrict e.hom U).flip ≪≫ pullbackLeftIsoSndIso e U.ι.imageι

/-- 概要：周辺同型で移した像の同型は周辺空間への射と可換（論文 補題 3.3）。
方針：二つの同型の射影公式と元の Cartesian 正方形の可換式を合成する。
規約：右辺の射は逆像開部分の実際の閉包含と周辺同型の hom。
使われ方：チャート基底への構造射の可換性。 -/
theorem openImageAmbientIso_hom_imageι (e : P ≅ Q) (U : Q.Opens) [QuasiCompact U.ι] :
    (openImageAmbientIso e U).hom ≫ U.ι.imageι = (e.hom ⁻¹ᵁ U).ι.imageι ≫ e.hom := by
  let a := imageOpenBaseChangeIsoOfIsPullback U.ι e.hom
    (e.hom ⁻¹ᵁ U).ι (e.hom ∣_ U) (isPullback_morphismRestrict e.hom U).flip
  have hs : (pullbackLeftIsoSndIso e U.ι.imageι).hom ≫ U.ι.imageι =
      pullback.fst e.hom U.ι.imageι ≫ e.hom :=
    (congrArg (· ≫ U.ι.imageι) (pullbackLeftIsoSndIso_hom e U.ι.imageι)).trans
      pullback.condition.symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (a.hom ≫ ·) hs).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ e.hom) (imageOpenBaseChangeIsoOfIsPullback_hom_fst _ _ _ _ _))))

/-- 概要：対応する二つの具体的な開部分のスキーム論的像の同型（論文 補題 3.3）。
方針：指定開部分と逆像開部分の等式、周辺同型による像の移送を合成する。
規約：開集合の対応は実際の等式として要求する。
使われ方：基本開のアフィン純変換の像と strict transform の周辺チャートの像。 -/
noncomputable def openImageAmbientIsoOfEq (e : P ≅ Q) (U : Q.Opens) (V : P.Opens)
    [QuasiCompact U.ι] (h : e.hom ⁻¹ᵁ U = V) : V.ι.image ≅ U.ι.image :=
  openImageCongrIso h.symm ≪≫ openImageAmbientIso e U

/-- 概要：具体的な開部分の像の同型は周辺空間への指定射を保つ（論文 補題 3.3）。
方針：開集合の等式による同型と周辺同型による移送の因子化式を合成する。
規約：同型の hom と実際の閉包含の可換式。
使われ方：平坦性を移す際の基底の保持。 -/
theorem openImageAmbientIsoOfEq_hom_imageι (e : P ≅ Q) (U : Q.Opens) (V : P.Opens)
    [QuasiCompact U.ι] (h : e.hom ⁻¹ᵁ U = V) :
    (openImageAmbientIsoOfEq e U V h).hom ≫ U.ι.imageι = V.ι.imageι ≫ e.hom :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (openImageAmbientIso_hom_imageι e U)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ e.hom) (openImageCongrIso_hom_imageι h.symm))))

end SerrePositivity.KST.Descent
