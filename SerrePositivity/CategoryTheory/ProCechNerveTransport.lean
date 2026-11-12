module

public import SerrePositivity.CategoryTheory.ProCechNerveData
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Whiskering

/-!
# pro Čech データの通常の関手による移送

## 概要
各有限冪を保つ関手に沿って、塔の Čech データと射影の両立を移す。

## 方針
各段には既存の Čech データの移送を適用し、遷移には右 whisker を使う。

## 規約
一般の極限の存在は仮定せず、指定した有限冪の保存だけを要求する。

## 使われ方
Berthelot III.4、Stacks 07HP。大きい結晶厚化の圏から小さいサイトへの移送。
-/

@[expose] public noncomputable section
universe u v u' v'
open scoped Simplicial
namespace CategoryTheory
open Limits
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {U : ℕ ⥤ C}

/-- 指定した有限冪を保つ関手による pro Čech データの移送。 -/
def ProCechNerveData.map (d : ProCechNerveData U) (F : C ⥤ D)
    (hF : ∀ e n : ℕ, PreservesLimit
      (Discrete.functor (fun _ : Fin (n + 1) => U.obj e)) F) :
    ProCechNerveData (U ⋙ F) where
  level e := (d.level e).map F (hF e)
  transition e := Functor.whiskerRight (d.transition e) F
  transition_proj e n i := by
    change F.map ((d.transition e).app (Opposite.op ⦋n⦌)) ≫
      F.map ((d.level (e + 1)).proj n i) =
        F.map ((d.level e).proj n i) ≫ F.map (U.map (homOfLE (Nat.le_succ e)))
    rw [← F.map_comp, ← F.map_comp, d.transition_proj]

/-- 圏同値による pro Čech データの移送。 -/
def ProCechNerveData.mapEquivalence (d : ProCechNerveData U) (e : C ≌ D) :
    ProCechNerveData (U ⋙ e.functor) :=
  d.map e.functor (fun _ _ => inferInstance)

end CategoryTheory
