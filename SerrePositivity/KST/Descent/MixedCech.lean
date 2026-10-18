module

public import SerrePositivity.KST.Descent.CechBaseChange
public import SerrePositivity.KST.Descent.CechTransferRetract

/-!
# 異なる二つの被覆の実際の混合二重 Čech 図式

## 概要
一つの射を別の射の全 Čech 段へ底変換し、全単体射を持つ混合二重 Čech 図式を構成する。

## 方針
基底上の対象から実際の底変換 Arrow を作る関手を構成し、Čech nerve 関手と合成する。

## 規約
二つの射を等しいとは仮定しない。通常の幾何的引き戻しを使い、値域の Tot は取らない。

## 使われ方
論文 補題 3.2・3.3 の有限平坦細分と元の被覆の比較。
原典の τ 位相の層論を二方向の Čech 計算と Fubini で置換する幾何入力。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {X W Y : C} (f : X ⟶ Y)

/-- 概要：基底上の各対象に元の射の実際の底変換 Arrow を対応させる（補題 3.2）。
方針：指定引き戻しの第二射影と引き戻しの map を使う。
規約：全ての Over の射に対する関手性を保持する。
使われ方：任意の別の Čech 図式上の混合底変換。 -/
noncomputable def overBaseChangeArrow : Over Y ⥤ Arrow C where
  obj Z := Arrow.mk (pullback.snd f Z.hom)
  map {Z Z'} α := Arrow.homMk
    (pullback.map f Z.hom f Z'.hom (𝟙 X) α.left (𝟙 Y)
      (Category.comp_id f |>.trans (Category.id_comp f).symm)
      ((Category.comp_id Z.hom).trans α.w.symm))
    α.left (pullback.lift_snd _ _ _)
  map_id Z := by
    apply Arrow.hom_ext
    · apply pullback.hom_ext <;> simp [pullback.map]
    · rfl
  map_comp α β := by
    apply Arrow.hom_ext
    · apply pullback.hom_ext <;> simp [pullback.map, PullbackCone.mk]
    · rfl

/-- 概要：各底変換 Arrow から元の射への指定比較は自然（補題 3.2）。
方針：引き戻しの map の第一射影公式と Over の可換式を使う。
規約：基底への構造射も同時に保持する。
使われ方：混合二重 Čech の全外側の単体射に関する第一射影の自然性。 -/
noncomputable def overBaseChangeArrowToOriginal :
    overBaseChangeArrow f ⟶ (Functor.const (Over Y)).obj (Arrow.mk f) where
  app Z := baseChangeArrowToOriginal f Z.hom
  naturality {Z Z'} α := by
    apply Arrow.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact α.w.trans (Category.comp_id Z.hom).symm

variable (g : W ⟶ Y)

/-- 概要：別の射の全 Čech 段へ底変換した元の射の Arrow 図式（補題 3.2）。
方針：実際の Over の Čech 図式を底変換 Arrow 関手へ合成する。
規約：非増強の全段と全ての面射・退化射を保持する。
使われ方：有限平坦な細分と元の被覆の混合二重 Čech。 -/
noncomputable def mixedCechBaseChange : SimplexCategoryᵒᵖ ⥤ Arrow C :=
  cechOverDiagram g ⋙ overBaseChangeArrow f

/-- 概要：異なる二つの射の実際の混合二重増強 Čech 図式（補題 3.2）。
方針：底変換 Arrow の図式へ増強 Čech nerve 関手を合成する。
規約：外側は g、内側は f の底変換の Čech。Tot や降下は結論しない。
使われ方：二つの方向の Čech 計算と Fubini の入力。 -/
noncomputable def mixedAugmentedCech : SimplexCategoryᵒᵖ ⥤ SimplicialObject.Augmented C :=
  mixedCechBaseChange f g ⋙ SimplicialObject.augmentedCechNerve

/-- 概要：混合二重 Čech の内側の元の Čech 段への第一射影（補題 3.2）。
方針：底変換 Arrow から元の射への指定比較を Čech nerve で写す。
規約：実際の指定射であり、選んだ切断ではない。
使われ方：混合図式を二つの Čech 段のファイバー積として表示する。 -/
noncomputable def mixedCechFirst (n m : SimplexCategoryᵒᵖ) :
    ((mixedAugmentedCech f g).obj n).left.obj m ⟶ (Arrow.mk f).cechNerve.obj m :=
  (Arrow.mapCechNerve (baseChangeArrowToOriginal f
    ((Arrow.mk g).augmentedCechNerve.hom.app n))).app m

/-- 概要：混合二重 Čech の外側の元の Čech 段への第二射影（補題 3.2）。
方針：各行の実際の増強を使う。
規約：元の g の Čech 段への指定増強射影。
使われ方：二つの元の Čech 段のファイバー積の第二射影。 -/
noncomputable def mixedCechSecond (n m : SimplexCategoryᵒᵖ) :
    ((mixedAugmentedCech f g).obj n).left.obj m ⟶ (Arrow.mk g).cechNerve.obj n :=
  ((mixedAugmentedCech f g).obj n).hom.app m

/-- 概要：混合二重 Čech の指定各段は二つの元の Čech 段の実際のファイバー積（補題 3.2）。
方針：Čech nerve の底変換の Cartesian 性を各内側次数で評価する。
規約：f と g は異なってよく、全単体次数を扱う。
使われ方：軸交換・細分比較・二方向の増強の幾何入力。 -/
theorem mixedCech_isPullback (n m : SimplexCategoryᵒᵖ) :
    IsPullback (mixedCechFirst f g n m) (mixedCechSecond f g n m)
      ((Arrow.mk f).augmentedCechNerve.hom.app m)
      ((Arrow.mk g).augmentedCechNerve.hom.app n) :=
  (baseChangeCech_isPullback f ((Arrow.mk g).augmentedCechNerve.hom.app n)).app m

/-- 概要：異なる二つの射と Čech 次数を交換する実際の標準同型（補題 3.2）。
方針：同じ二つの増強のファイバー積の二射影を交換する。
規約：自然性と Tot の Fubini は別工程。
使われ方：元の被覆と有限平坦な細分を二つの方向で比較する。 -/
noncomputable def mixedCechSwapIso (n m : SimplexCategoryᵒᵖ) :
    ((mixedAugmentedCech f g).obj n).left.obj m ≅
      ((mixedAugmentedCech g f).obj m).left.obj n :=
  (mixedCech_isPullback f g n m).isoIsPullback _ _ (mixedCech_isPullback g f m n).flip

/-- 概要：混合軸交換は第一射影を交換先の第二射影へ移す（補題 3.2）。
方針：ファイバー積の標準同型の第一射影公式。
規約：指定二射影の等式。使われ方：全単体射との自然性の検査。 -/
@[reassoc] theorem mixedCechSwapIso_first (n m : SimplexCategoryᵒᵖ) :
    (mixedCechSwapIso f g n m).hom ≫ mixedCechSecond g f m n = mixedCechFirst f g n m :=
  (mixedCech_isPullback f g n m).isoIsPullback_hom_fst _ _
    (mixedCech_isPullback g f m n).flip

/-- 概要：混合軸交換は第二射影を交換先の第一射影へ移す（補題 3.2）。
方針：ファイバー積の標準同型の第二射影公式。
規約：指定二射影の等式。使われ方：全単体射との自然性の検査。 -/
@[reassoc] theorem mixedCechSwapIso_second (n m : SimplexCategoryᵒᵖ) :
    (mixedCechSwapIso f g n m).hom ≫ mixedCechFirst g f m n = mixedCechSecond f g n m :=
  (mixedCech_isPullback f g n m).isoIsPullback_hom_snd _ _
    (mixedCech_isPullback g f m n).flip

end SerrePositivity.KST.Descent
