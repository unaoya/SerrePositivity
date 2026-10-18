module

public import SerrePositivity.KST.Descent.FiniteTypeLimits
public import SerrePositivity.KST.Descent.MixedCech

/-!
# 指定された有限型の圏の底変換の関手性

## 概要
実際のスキームの引き戻しから構成した finiteTypePullback を、基底上の全射に関する関手にする。

## 方針
指定 Cartesian 正方形の普遍性で射を作り、二射影で恒等射・合成を検査する。

## 規約
圏の選択された pullback に対象を置き換えず、元の指定モデルを使う。

## 使われ方
論文 補題 3.2・3.3 の Čech 全単体射における抽象 blowup 底変換の関手性。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S} (f : X ⟶ Y)

/-- 概要：指定された有限型の引き戻しの基底変更の射（補題 3.3）。
方針：同じ第一射影と底の射を合成した第二射影を普遍性へ入れる。
規約：対象は実際の finiteTypePullback。使われ方：Čech の全単体射への作用。 -/
noncomputable def finiteTypeBaseChangeMap {Z Z' : Over Y} (α : Z ⟶ Z') :
    finiteTypePullback f Z.hom ⟶ finiteTypePullback f Z'.hom :=
  (finiteTypePullback_isPullback f Z'.hom).lift (finiteTypePullbackFst f Z.hom)
    (finiteTypePullbackSnd f Z.hom ≫ α.left)
    ((finiteTypePullback_comm f Z.hom).trans
      ((congrArg (finiteTypePullbackSnd f Z.hom ≫ ·) α.w.symm).trans
        (Category.assoc _ _ _).symm))

/-- 概要：指定底変換の map は第一射影を保つ（補題 3.3）。方針：lift の射影公式を使う。
規約：指定射そのものの等式。使われ方：関手の法則と比較立方体の自然性。 -/
@[reassoc (attr := simp)] theorem finiteTypeBaseChangeMap_fst {Z Z' : Over Y} (α : Z ⟶ Z') :
    finiteTypeBaseChangeMap f α ≫ finiteTypePullbackFst f Z'.hom =
      finiteTypePullbackFst f Z.hom :=
  (finiteTypePullback_isPullback f Z'.hom).lift_fst _ _ _

/-- 概要：指定底変換の map は第二射影に底の射を合成する（補題 3.3）。方針：lift の射影公式。
規約：元の底の射を保持する。使われ方：関手の法則と Čech 増強の自然性。 -/
@[reassoc (attr := simp)] theorem finiteTypeBaseChangeMap_snd {Z Z' : Over Y} (α : Z ⟶ Z') :
    finiteTypeBaseChangeMap f α ≫ finiteTypePullbackSnd f Z'.hom =
      finiteTypePullbackSnd f Z.hom ≫ α.left :=
  (finiteTypePullback_isPullback f Z'.hom).lift_snd _ _ _

/-- 概要：指定底変換の map は恒等射を保つ（補題 3.3）。方針：二射影で検査する。
規約：有限型の圏内の実際の等式。使われ方：元の指定底変換の関手性。 -/
@[simp] theorem finiteTypeBaseChangeMap_id (Z : Over Y) :
    finiteTypeBaseChangeMap f (𝟙 Z) = 𝟙 (finiteTypePullback f Z.hom) := by
  apply (finiteTypePullback_isPullback f Z.hom).hom_ext <;> simp

/-- 概要：指定底変換の map は合成を保つ（補題 3.3）。方針：二射影と結合律で検査する。
規約：型クラスの別の引き戻しへ変更しない。使われ方：Čech 全単体射の整合性。 -/
theorem finiteTypeBaseChangeMap_comp {Z Z' Z'' : Over Y} (α : Z ⟶ Z') (β : Z' ⟶ Z'') :
    finiteTypeBaseChangeMap f α ≫ finiteTypeBaseChangeMap f β =
      finiteTypeBaseChangeMap f (α ≫ β) := by
  apply (finiteTypePullback_isPullback f Z''.hom).hom_ext <;> simp [Category.assoc]

/-- 概要：指定された有限型の引き戻しによる底変換 Arrow の関手（補題 3.3）。
方針：実際の第二射影を対象とし、構成した map と底の射で Arrow の射を作る。
規約：選択された圏論的 pullback との比較は別に明示する。
使われ方：実際の抽象 blowup の右辺・中心の底変換を全 Čech 図式へまとめる。 -/
noncomputable def finiteTypeOverBaseChangeArrow : Over Y ⥤ Arrow (FiniteTypeSchemes S) where
  obj Z := Arrow.mk (finiteTypePullbackSnd f Z.hom)
  map α := Arrow.homMk (finiteTypeBaseChangeMap f α) α.left (finiteTypeBaseChangeMap_snd f α)
  map_id Z := by
    apply Arrow.hom_ext
    · exact finiteTypeBaseChangeMap_id f Z
    · rfl
  map_comp α β := by
    apply Arrow.hom_ext
    · exact (finiteTypeBaseChangeMap_comp f α β).symm
    · rfl

/-- 概要：指定底変換から元の射への Arrow 比較は自然（補題 3.3）。
方針：第一射影の保存と Over の可換式で検査する。
規約：同じ有限型の圏内の実際の自然変換。
使われ方：自然な抽象 blowup 列を全 Čech 段で比較する。 -/
noncomputable def finiteTypeOverBaseChangeToOriginal :
    finiteTypeOverBaseChangeArrow f ⟶ (Functor.const (Over Y)).obj (Arrow.mk f) where
  app Z := Arrow.homMk (finiteTypePullbackFst f Z.hom) Z.hom (finiteTypePullback_comm f Z.hom)
  naturality {Z Z'} α := by
    apply Arrow.hom_ext
    · exact (finiteTypeBaseChangeMap_fst f α).trans (Category.comp_id _).symm
    · exact α.w.trans (Category.comp_id _).symm

end SerrePositivity.KST.Descent
