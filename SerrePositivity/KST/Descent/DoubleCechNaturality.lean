module

public import SerrePositivity.KST.Descent.DoubleCechGeometry
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# 二重 Čech の軸交換と単体射の整合性

## 概要
二つの軸の単体射について二射影の自然性を示し、軸交換が単体射と可換することを証明する。

## 方針
実際の増強 Čech の関手性と自然性を二射影で検査する。

## 規約
零番目の射影から選ぶ切断の自然性は使わない。値域の Tot の交換は別工程。

## 使われ方
論文 補題 3.2 の二方向の Čech 計算の比較と、Fubini・細分のための幾何入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S} (f : X ⟶ Y)

/-- 概要：内側の単体射から二重 Čech の射を取る（論文 補題 3.2）。
方針：各行の元の関手を使う。
規約：実際の図式の射を保持する。
使われ方：軸交換の自然性の内側の辺。 -/
noncomputable def doubleCechInnerMap (n : SimplexCategoryᵒᵖ)
    {m m' : SimplexCategoryᵒᵖ} (α : m ⟶ m') :
    ((finiteTypeDoubleCech f).obj n).left.obj m ⟶
      ((finiteTypeDoubleCech f).obj n).left.obj m' :=
  ((finiteTypeDoubleCech f).obj n).left.map α

/-- 概要：外側の単体射から二重 Čech の射を取る（論文 補題 3.2）。
方針：実際の二重 Čech 関手の射を内側の次数で評価する。
規約：実際の図式の射を保持する。
使われ方：軸交換の自然性の外側の辺。 -/
noncomputable def doubleCechOuterMap {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (m : SimplexCategoryᵒᵖ) :
    ((finiteTypeDoubleCech f).obj n).left.obj m ⟶
      ((finiteTypeDoubleCech f).obj n').left.obj m :=
  ((finiteTypeDoubleCech f).map α).left.app m

/-- 概要：内側の射と第一射影は自然（論文 補題 3.2）。
方針：元の Čech への自然変換の自然性を使う。
規約：全ての単体射を扱う。
使われ方：軸交換の二射影での検査。 -/
@[reassoc] theorem doubleCechInnerMap_first (n : SimplexCategoryᵒᵖ)
    {m m' : SimplexCategoryᵒᵖ} (α : m ⟶ m') :
    doubleCechInnerMap f n α ≫ doubleCechFirst f n m' =
      doubleCechFirst f n m ≫ (finiteTypeAugmentedCech f).left.map α :=
  (Arrow.mapCechNerve
    (baseChangeArrowToOriginal f ((finiteTypeAugmentedCech f).hom.app n))).naturality α

/-- 概要：内側の射は外側への射影を保つ（論文 補題 3.2）。
方針：各行の増強の自然性と定数図式の恒等射を使う。
規約：切断の自然性ではない。
使われ方：軸交換の二射影での検査。 -/
@[reassoc] theorem doubleCechInnerMap_second (n : SimplexCategoryᵒᵖ)
    {m m' : SimplexCategoryᵒᵖ} (α : m ⟶ m') :
    doubleCechInnerMap f n α ≫ doubleCechSecond f n m' = doubleCechSecond f n m :=
  (((finiteTypeDoubleCech f).obj n).hom.naturality α).trans (Category.comp_id _)

/-- 概要：外側の射と第二射影は自然（論文 補題 3.2）。
方針：実際の増強 Čech の射の可換性を評価する。
規約：全ての単体射を扱う。
使われ方：軸交換の二射影での検査。 -/
@[reassoc] theorem doubleCechOuterMap_second {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (m : SimplexCategoryᵒᵖ) :
    doubleCechOuterMap f α m ≫ doubleCechSecond f n' m =
      doubleCechSecond f n m ≫ (finiteTypeAugmentedCech f).left.map α :=
  congrArg (fun η ↦ η.app m) ((finiteTypeDoubleCech f).map α).w

/-- 概要：外側の射は内側への射影を保つ（論文 補題 3.2）。
方針：Arrow の底変換射と元の射への比較の合成を検査し、Čech の関手性で写す。
規約：元の Čech への指定比較を保持する。
使われ方：軸交換の二射影での検査。 -/
@[reassoc] theorem doubleCechOuterMap_first {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (m : SimplexCategoryᵒᵖ) :
    doubleCechOuterMap f α m ≫ doubleCechFirst f n' m = doubleCechFirst f n m := by
  let a := (finiteTypeCechBaseChange f).map α
  let b := baseChangeArrowToOriginal f ((finiteTypeAugmentedCech f).hom.app n')
  let c := baseChangeArrowToOriginal f ((finiteTypeAugmentedCech f).hom.app n)
  have comp : a ≫ b = c := by
    apply Arrow.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact ((finiteTypeAugmentedCech f).hom.naturality α).trans (Category.comp_id _)
  have hc : Arrow.mapCechNerve a ≫ Arrow.mapCechNerve b = Arrow.mapCechNerve c :=
    ((SimplicialObject.cechNerve (C := FiniteTypeSchemes S)).map_comp a b).symm.trans
      (congrArg (fun k ↦ Arrow.mapCechNerve k) comp)
  exact congrArg (fun η ↦ η.app m) hc

/-- 概要：軸交換は内側の単体射を外側の単体射に移す（論文 補題 3.2）。
方針：比較先の二射影で自然性を検査する。
規約：全単体次数と全ての単体射についての等式。
使われ方：二重図式全体の交換と Fubini の幾何入力。 -/
theorem doubleCechSwapIso_inner_naturality (n : SimplexCategoryᵒᵖ)
    {m m' : SimplexCategoryᵒᵖ} (α : m ⟶ m') :
    doubleCechInnerMap f n α ≫ (doubleCechSwapIso f n m').hom =
      (doubleCechSwapIso f n m).hom ≫ doubleCechOuterMap f α n := by
  apply (doubleCech_isPullback f m' n).hom_ext
  · simp only [Category.assoc, doubleCechSwapIso_second, doubleCechOuterMap_first,
      doubleCechInnerMap_second]
  · simp only [Category.assoc, doubleCechSwapIso_first, doubleCechOuterMap_second,
      doubleCechInnerMap_first, doubleCechSwapIso_first_assoc]

/-- 概要：軸交換は外側の単体射を内側の単体射に移す（論文 補題 3.2）。
方針：比較先の二射影で自然性を検査する。
規約：全単体次数と全ての単体射についての等式。
使われ方：二重図式全体の交換と Fubini の幾何入力。 -/
theorem doubleCechSwapIso_outer_naturality {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (m : SimplexCategoryᵒᵖ) :
    doubleCechOuterMap f α m ≫ (doubleCechSwapIso f n' m).hom =
      (doubleCechSwapIso f n m).hom ≫ doubleCechInnerMap f m α := by
  apply (doubleCech_isPullback f m n').hom_ext
  · simp only [Category.assoc, doubleCechSwapIso_second, doubleCechInnerMap_first,
      doubleCechOuterMap_second, doubleCechSwapIso_second_assoc]
  · simp only [Category.assoc, doubleCechSwapIso_first, doubleCechInnerMap_second,
      doubleCechOuterMap_first]

/-- 概要：実際の二重 Čech を積添字の一つの関手にする（論文 補題 3.2）。
方針：増強を忘れて二重関手を uncurry する。
規約：二つの方向の全ての単体射を保持する。
使われ方：軸交換を二重図式全体の自然同型として扱う。 -/
noncomputable def doubleCechBifunctor :
    SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ FiniteTypeSchemes S :=
  Functor.uncurry.obj (finiteTypeDoubleCech f ⋙ SimplicialObject.Augmented.drop)

/-- 概要：二重 Čech の軸交換は図式全体の自然同型（論文 補題 3.2）。
方針：内側と外側それぞれの自然性を、積添字の射の合成に適用する。
規約：値域の Tot の Fubini の証明とは区別する。
使われ方：二方向の Čech 計算の幾何的な交換。 -/
noncomputable def doubleCechSwapNatIso :
    doubleCechBifunctor f ≅ CategoryTheory.Prod.swap _ _ ⋙ doubleCechBifunctor f :=
  NatIso.ofComponents (fun nm ↦ doubleCechSwapIso f nm.1 nm.2) (fun {nm nm'} α ↦ by
    change (doubleCechOuterMap f α.1 nm.2 ≫ doubleCechInnerMap f nm'.1 α.2) ≫
        (doubleCechSwapIso f nm'.1 nm'.2).hom =
      (doubleCechSwapIso f nm.1 nm.2).hom ≫
        (doubleCechOuterMap f α.2 nm.1 ≫ doubleCechInnerMap f nm'.2 α.1)
    rw [Category.assoc, doubleCechSwapIso_inner_naturality,
      ← Category.assoc, doubleCechSwapIso_outer_naturality, Category.assoc]
    exact congrArg ((doubleCechSwapIso f nm.1 nm.2).hom ≫ ·)
      (((finiteTypeDoubleCech f).map α.2).left.naturality α.1))

end SerrePositivity.KST.Descent
