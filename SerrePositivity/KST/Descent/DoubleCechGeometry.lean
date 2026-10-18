module

public import SerrePositivity.KST.Descent.CechBaseChange
public import SerrePositivity.KST.Descent.FiniteTypeCech

/-!
# 実際の二重 Čech 各段のファイバー積と軸交換

## 概要
実際の二重 Čech 各段を二つの Čech 段のファイバー積として検査し、軸交換同型を構成する。

## 方針
全単体次数の Čech 底変換比較を評価し、指定二射影の普遍性で交換する。

## 規約
本ファイルの交換は各二重次数の指定同型。自然性は DoubleCechNaturality、Tot の Fubini は別工程。

## 使われ方
論文 補題 3.2 の二重 Čech による τ 位相の層論の置換に必要な幾何。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S} (f : X ⟶ Y)

/-- 概要：二重 Čech から内側の元の Čech 段への指定射影（論文 補題 3.2）。
方針：底変換した射から元の射への Arrow の射を Čech nerve で写す。
規約：元の有限型の圏内の指定射。
使われ方：二つの Čech 段のファイバー積の第一射影。 -/
noncomputable def doubleCechFirst (n m : SimplexCategoryᵒᵖ) :
    ((finiteTypeDoubleCech f).obj n).left.obj m ⟶ (finiteTypeAugmentedCech f).left.obj m :=
  (Arrow.mapCechNerve (baseChangeArrowToOriginal f ((finiteTypeAugmentedCech f).hom.app n))).app m

/-- 概要：二重 Čech から外側の Čech 段への指定射影（論文 補題 3.2）。
方針：各行の Čech nerve の増強を使う。
規約：切断を選ぶ射ではなく、実際の増強射影。
使われ方：二つの Čech 段のファイバー積の第二射影。 -/
noncomputable def doubleCechSecond (n m : SimplexCategoryᵒᵖ) :
    ((finiteTypeDoubleCech f).obj n).left.obj m ⟶ (finiteTypeAugmentedCech f).left.obj n :=
  ((finiteTypeDoubleCech f).obj n).hom.app m

/-- 概要：二重 Čech の指定各段は二つの Čech 段の実際のファイバー積（論文 補題 3.2）。
方針：図式全体の Čech 底変換の Cartesian 性を内側の次数で評価する。
規約：対象の同型の存在でなく、指定二射影の Cartesian 性を結論する。
使われ方：軸交換と細分比較の普遍性。 -/
theorem doubleCech_isPullback (n m : SimplexCategoryᵒᵖ) :
    IsPullback (doubleCechFirst f n m) (doubleCechSecond f n m)
      ((finiteTypeAugmentedCech f).hom.app m) ((finiteTypeAugmentedCech f).hom.app n) :=
  (baseChangeCech_isPullback f ((finiteTypeAugmentedCech f).hom.app n)).app m

/-- 概要：実際の二重 Čech の二つの次数の交換同型（論文 補題 3.2）。
方針：同じ二つの増強のファイバー積の普遍性で、二射影を交換する。
規約：同型の二射影との合成を後続で明示する。
使われ方：二つの方向の Čech 計算を比較する幾何入力。 -/
noncomputable def doubleCechSwapIso (n m : SimplexCategoryᵒᵖ) :
    ((finiteTypeDoubleCech f).obj n).left.obj m ≅
      ((finiteTypeDoubleCech f).obj m).left.obj n :=
  (doubleCech_isPullback f n m).isoIsPullback _ _ (doubleCech_isPullback f m n).flip

/-- 概要：軸交換は第一射影を第二射影へ移す（論文 補題 3.2）。
方針：二つのファイバー積の標準同型の第一射影の公式。
規約：実際の指定二射影の等式。
使われ方：交換を元の Čech 図式の比較へ接続する。 -/
@[reassoc] theorem doubleCechSwapIso_first (n m : SimplexCategoryᵒᵖ) :
    (doubleCechSwapIso f n m).hom ≫ doubleCechSecond f m n = doubleCechFirst f n m :=
  (doubleCech_isPullback f n m).isoIsPullback_hom_fst _ _ (doubleCech_isPullback f m n).flip

/-- 概要：軸交換は第二射影を第一射影へ移す（論文 補題 3.2）。
方針：二つのファイバー積の標準同型の第二射影の公式。
規約：実際の指定二射影の等式。
使われ方：交換の二回の合成を検査する。 -/
@[reassoc] theorem doubleCechSwapIso_second (n m : SimplexCategoryᵒᵖ) :
    (doubleCechSwapIso f n m).hom ≫ doubleCechFirst f m n = doubleCechSecond f n m :=
  (doubleCech_isPullback f n m).isoIsPullback_hom_snd _ _ (doubleCech_isPullback f m n).flip

/-- 概要：実際の二重 Čech の軸交換を二回行うと恒等同型（論文 補題 3.2）。
方針：指定二射影で合成を検査する。
規約：点ごとの恒等ではなく有限型の圏内の同型の等式。
使われ方：二方向の比較を往復する際の整合性。 -/
theorem doubleCechSwapIso_involutive (n m : SimplexCategoryᵒᵖ) :
    doubleCechSwapIso f n m ≪≫ doubleCechSwapIso f m n = Iso.refl _ := by
  apply Iso.ext
  apply (doubleCech_isPullback f n m).hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (doubleCechSwapIso_second f m n)).trans
        ((doubleCechSwapIso_first f n m).trans (Category.id_comp _).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (doubleCechSwapIso_first f m n)).trans
        ((doubleCechSwapIso_second f n m).trans (Category.id_comp _).symm))

end SerrePositivity.KST.Descent
