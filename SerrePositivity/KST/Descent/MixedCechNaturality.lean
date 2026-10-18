module

public import SerrePositivity.KST.Descent.MixedCech
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# 異なる二つの被覆の混合 Čech の軸交換の自然性

## 概要
混合二重 Čech の二射影と単体射の整合性を証明し、二つの射を交換する自然同型を構成する。

## 方針
元の増強と Arrow の比較の自然性を二射影で検査し、積添字でまとめる。

## 規約
全ての面射・退化射を扱う。選んだ切断の自然性や Tot の Fubini は仮定しない。

## 使われ方
論文 補題 3.2・3.3 の有限平坦細分と元の被覆を二方向の Čech 計算で比較する幾何入力。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {X W Y : C} (f : X ⟶ Y) (g : W ⟶ Y)

/-- 概要：混合 Čech の内側の単体射（補題 3.2）。方針：各行の関手の射を使う。
規約：実際の図式の射。使われ方：軸交換の内側の自然性。 -/
noncomputable def mixedCechInnerMap (n : SimplexCategoryᵒᵖ)
    {m m' : SimplexCategoryᵒᵖ} (α : m ⟶ m') :
    ((mixedAugmentedCech f g).obj n).left.obj m ⟶
      ((mixedAugmentedCech f g).obj n).left.obj m' :=
  ((mixedAugmentedCech f g).obj n).left.map α

/-- 概要：混合 Čech の外側の単体射（補題 3.2）。方針：行の比較を内側の次数で評価する。
規約：実際の図式の射。使われ方：軸交換の外側の自然性。 -/
noncomputable def mixedCechOuterMap {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (m : SimplexCategoryᵒᵖ) :
    ((mixedAugmentedCech f g).obj n).left.obj m ⟶
      ((mixedAugmentedCech f g).obj n').left.obj m :=
  ((mixedAugmentedCech f g).map α).left.app m

/-- 概要：内側の単体射と第一射影の自然性（補題 3.2）。方針：Čech 比較の自然性を使う。
規約：異なる f と g に対して成立。使われ方：交換同型の二射影での検査。 -/
@[reassoc] theorem mixedCechInnerMap_first (n : SimplexCategoryᵒᵖ)
    {m m' : SimplexCategoryᵒᵖ} (α : m ⟶ m') :
    mixedCechInnerMap f g n α ≫ mixedCechFirst f g n m' =
      mixedCechFirst f g n m ≫ (Arrow.mk f).cechNerve.map α :=
  (Arrow.mapCechNerve (baseChangeArrowToOriginal f
    ((Arrow.mk g).augmentedCechNerve.hom.app n))).naturality α

/-- 概要：内側の単体射は第二射影を保つ（補題 3.2）。方針：各行の増強の自然性を使う。
規約：切断の自然性ではない。使われ方：交換同型の二射影での検査。 -/
@[reassoc] theorem mixedCechInnerMap_second (n : SimplexCategoryᵒᵖ)
    {m m' : SimplexCategoryᵒᵖ} (α : m ⟶ m') :
    mixedCechInnerMap f g n α ≫ mixedCechSecond f g n m' = mixedCechSecond f g n m :=
  (((mixedAugmentedCech f g).obj n).hom.naturality α).trans (Category.comp_id _)

/-- 概要：外側の単体射と第二射影の自然性（補題 3.2）。方針：増強対象の比較の可換式を評価する。
規約：全単体射についての等式。使われ方：交換同型の二射影での検査。 -/
@[reassoc] theorem mixedCechOuterMap_second {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (m : SimplexCategoryᵒᵖ) :
    mixedCechOuterMap f g α m ≫ mixedCechSecond f g n' m =
      mixedCechSecond f g n m ≫ (Arrow.mk g).cechNerve.map α :=
  congrArg (fun η ↦ η.app m) ((mixedAugmentedCech f g).map α).w

/-- 概要：外側の単体射は第一射影を保つ（補題 3.2）。方針：Over 全体での比較の自然性を使う。
規約：元の f の Čech への指定比較を保持。使われ方：交換同型の二射影での検査。 -/
@[reassoc] theorem mixedCechOuterMap_first {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (m : SimplexCategoryᵒᵖ) :
    mixedCechOuterMap f g α m ≫ mixedCechFirst f g n' m = mixedCechFirst f g n m := by
  let a := (mixedCechBaseChange f g).map α
  let b := baseChangeArrowToOriginal f ((Arrow.mk g).augmentedCechNerve.hom.app n')
  let c := baseChangeArrowToOriginal f ((Arrow.mk g).augmentedCechNerve.hom.app n)
  have hcomp : a ≫ b = c :=
    ((overBaseChangeArrowToOriginal f).naturality ((cechOverDiagram g).map α)).trans
      (Category.comp_id _)
  have hc : Arrow.mapCechNerve a ≫ Arrow.mapCechNerve b = Arrow.mapCechNerve c :=
    ((SimplicialObject.cechNerve (C := C)).map_comp a b).symm.trans
      (congrArg (fun k ↦ Arrow.mapCechNerve k) hcomp)
  exact congrArg (fun η ↦ η.app m) hc

/-- 概要：混合軸交換は内側の単体射を交換先の外側の射へ移す（補題 3.2）。
方針：交換先の二射影で四つの自然性を使う。
規約：f と g 自体も交換する。使われ方：二重図式全体の自然同型。 -/
theorem mixedCechSwapIso_inner_naturality (n : SimplexCategoryᵒᵖ)
    {m m' : SimplexCategoryᵒᵖ} (α : m ⟶ m') :
    mixedCechInnerMap f g n α ≫ (mixedCechSwapIso f g n m').hom =
      (mixedCechSwapIso f g n m).hom ≫ mixedCechOuterMap g f α n := by
  apply (mixedCech_isPullback g f m' n).hom_ext
  · simp only [Category.assoc, mixedCechSwapIso_second, mixedCechOuterMap_first,
      mixedCechInnerMap_second]
  · simp only [Category.assoc, mixedCechSwapIso_first, mixedCechOuterMap_second,
      mixedCechInnerMap_first, mixedCechSwapIso_first_assoc]

/-- 概要：混合軸交換は外側の単体射を交換先の内側の射へ移す（補題 3.2）。
方針：交換先の二射影で四つの自然性を使う。
規約：全ての面射・退化射を含む。使われ方：二重図式全体の自然同型。 -/
theorem mixedCechSwapIso_outer_naturality {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (m : SimplexCategoryᵒᵖ) :
    mixedCechOuterMap f g α m ≫ (mixedCechSwapIso f g n' m).hom =
      (mixedCechSwapIso f g n m).hom ≫ mixedCechInnerMap g f m α := by
  apply (mixedCech_isPullback g f m n').hom_ext
  · simp only [Category.assoc, mixedCechSwapIso_second, mixedCechInnerMap_first,
      mixedCechOuterMap_second, mixedCechSwapIso_second_assoc]
  · simp only [Category.assoc, mixedCechSwapIso_first, mixedCechInnerMap_second,
      mixedCechOuterMap_first]

/-- 概要：二つの射と軸の交換を二回行うと恒等同型（補題 3.2）。
方針：同じファイバー積の指定二射影で合成を検査する。
規約：実際の同型の等式。使われ方：二方向の混合 Čech 計算の往復の整合性。 -/
theorem mixedCechSwapIso_involutive (n m : SimplexCategoryᵒᵖ) :
    mixedCechSwapIso f g n m ≪≫ mixedCechSwapIso g f m n = Iso.refl _ := by
  apply Iso.ext
  apply (mixedCech_isPullback f g n m).hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (mixedCechSwapIso_second g f m n)).trans
        ((mixedCechSwapIso_first f g n m).trans (Category.id_comp _).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (mixedCechSwapIso_first g f m n)).trans
        ((mixedCechSwapIso_second f g n m).trans (Category.id_comp _).symm))

/-- 概要：混合二重 Čech を積添字の一つの関手にする（補題 3.2）。
方針：増強を忘れて二重関手を uncurry する。
規約：両方向の全単体射を保持する。使われ方：軸交換の自然同型と Fubini の幾何入力。 -/
noncomputable def mixedCechBifunctor : SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ C :=
  Functor.uncurry.obj (mixedAugmentedCech f g ⋙ SimplicialObject.Augmented.drop)

/-- 概要：二つの異なる射と二つの Čech 軸の交換は図式全体の自然同型（補題 3.2）。
方針：内側・外側の自然性と行間の比較の自然性を積添字で合成する。
規約：値域の Tot の交換や降下の結論は別に必要。
使われ方：有限平坦細分と元の被覆の二方向の実際の Čech 計算。 -/
noncomputable def mixedCechSwapNatIso :
    mixedCechBifunctor f g ≅ CategoryTheory.Prod.swap _ _ ⋙ mixedCechBifunctor g f :=
  NatIso.ofComponents (fun nm ↦ mixedCechSwapIso f g nm.1 nm.2) (fun {nm nm'} α ↦ by
    change (mixedCechOuterMap f g α.1 nm.2 ≫ mixedCechInnerMap f g nm'.1 α.2) ≫
        (mixedCechSwapIso f g nm'.1 nm'.2).hom =
      (mixedCechSwapIso f g nm.1 nm.2).hom ≫
        (mixedCechOuterMap g f α.2 nm.1 ≫ mixedCechInnerMap g f nm'.2 α.1)
    rw [Category.assoc, mixedCechSwapIso_inner_naturality,
      ← Category.assoc, mixedCechSwapIso_outer_naturality, Category.assoc]
    exact congrArg ((mixedCechSwapIso f g nm.1 nm.2).hom ≫ ·)
      (((mixedAugmentedCech g f).map α.2).left.naturality α.1))

end SerrePositivity.KST.Descent
