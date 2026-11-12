module

public import SerrePositivity.HomologicalAlgebra.CoendAdditive
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all SerrePositivity.HomologicalAlgebra.CoendAdditive

/-!
# 加群重みと非有界複体図式の線形 coend

## 概要
加群値の反変重みを次数零の複体へ入れ、元の複体図式とテンソルした coend を取る。

## 方針
single と全テンソル関手、図式への後合成、同じ coend 関手を合成する。

## 規約
係数の複体は非有界でよい。重みの射の像も元の同じテンソルと coend の射である。

## 使われ方
HA 1.2.4、Weibel §2.2。重みの指定鎖ホモトピーを計算複体の同じ比較射へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 一つの加群重みの値を、次数零に入れて元の全複体図式とテンソルする。 -/
def moduleWeightTensor (X : J ⥤ Complex A) : ModuleCat.{u} A ⥤ J ⥤ Complex A :=
  HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0 ⋙ curriedTensor (Complex A) ⋙
    (Functor.whiskeringLeft J (Complex A) (Complex A)).obj X

/-- 重みの全対象・全射を、同じ元の図式とのテンソルの二変数図式へ送る。 -/
def linearWeightBifunctor (X : J ⥤ Complex A) :
    (Jᵒᵖ ⥤ ModuleCat.{u} A) ⥤ Jᵒᵖ ⥤ J ⥤ Complex A :=
  (Functor.whiskeringRight Jᵒᵖ (ModuleCat.{u} A) (J ⥤ Complex A)).obj (moduleWeightTensor A X)

/-- 元の複体図式を係数とする、加群重みの同じ線形 coend の関手。 -/
def linearWeightRealization (X : J ⥤ Complex A) : (Jᵒᵖ ⥤ ModuleCat.{u} A) ⥤ Complex A :=
  linearWeightBifunctor A X ⋙ coendFunctor J (Complex A)

/-- テンソル前の single と全図式のテンソルは、重みの射に加法的。 -/
instance moduleWeightTensor_additive (X : J ⥤ Complex A) : (moduleWeightTensor A X).Additive := by
  dsimp [moduleWeightTensor]
  infer_instance

/-- 元の図式とテンソルする二変数図式の関手は、重みに加法的。 -/
instance linearWeightBifunctor_additive (X : J ⥤ Complex A) :
    (linearWeightBifunctor A X).Additive := by
  dsimp [linearWeightBifunctor]
  infer_instance

/-- 同じ線形 coend 関手は重みの射の加法性を保つ。 -/
instance linearWeightRealization_additive (X : J ⥤ Complex A) :
    (linearWeightRealization A X).Additive := by
  dsimp [linearWeightRealization]
  infer_instance

/-- 元の複体図式の射も保持する、次数零テンソルの全関手族。 -/
def moduleWeightTensorFamily : (J ⥤ Complex A) ⥤ ModuleCat.{u} A ⥤ J ⥤ Complex A :=
  (Functor.whiskeringRight J (Complex A) (ModuleCat.{u} A ⥤ Complex A)).obj
    ((curriedTensor (Complex A)).flip ⋙
      (Functor.whiskeringLeft (ModuleCat.{u} A) (Complex A) (Complex A)).obj
        (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0)) ⋙
    flipFunctor J (ModuleCat.{u} A) (Complex A)

/-- 重みと元の図式を両方動かす、実際の同じ線形 coend の全関手。 -/
def linearWeightRealizationBifunctor :
    (J ⥤ Complex A) ⥤ (Jᵒᵖ ⥤ ModuleCat.{u} A) ⥤ Complex A :=
  moduleWeightTensorFamily A ⋙
    Functor.whiskeringRight Jᵒᵖ (ModuleCat.{u} A) (J ⥤ Complex A) ⋙
    (Functor.whiskeringRight (Jᵒᵖ ⥤ ModuleCat.{u} A)
      (Jᵒᵖ ⥤ J ⥤ Complex A) (Complex A)).obj (coendFunctor J (Complex A))

/-- 全関手族の各値は、元の同じ係数図式の線形 coend 関手。 -/
theorem linearWeightRealizationBifunctor_obj (X : J ⥤ Complex A) :
    (linearWeightRealizationBifunctor A).obj X = linearWeightRealization A X := rfl

/-- 重みの比較射は、元の係数図式のすべての射と同じ正方形で両立する。 -/
theorem linearWeightRealization_naturality {X Y : J ⥤ Complex A} (η : X ⟶ Y)
    {W V : Jᵒᵖ ⥤ ModuleCat.{u} A} (α : W ⟶ V) :
    (linearWeightRealization A X).map α ≫
        ((linearWeightRealizationBifunctor A).map η).app V =
      ((linearWeightRealizationBifunctor A).map η).app W ≫
        (linearWeightRealization A Y).map α :=
  ((linearWeightRealizationBifunctor A).map η).naturality α

end SerrePositivity.HomologicalAlgebra
