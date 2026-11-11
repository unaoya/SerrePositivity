module

public import SerrePositivity.CategoryTheory.CechNerveData
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# 塔の Čech 脈体の通常の圏論的データ

## 概要
各段の指定された有限冪を持つ塔と、その pro 弱終性を扱う。

## 方針
段の遷移から自然数上の関手を作り、反対圏と uncurry で二重添字を得る。

## 規約
サイトの向きで塔は ℕ 上、前層を評価する添字は ℕᵒᵖ × Δ。

## 使われ方
BS 著者版 Theorem 5.2、Stacks 07HP。結晶分冪包の有限冪商の塔。
∞ 圏の極限や層コホモロジーはここでは扱わない。
-/

@[expose] public noncomputable section
universe u v u' v'
open scoped Simplicial
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- 任意の対象から、塔のある段への射が存在する。 -/
def IsProWeaklyTerminal (U : ℕ ⥤ C) : Prop :=
  ∀ V : C, ∃ e : ℕ, Nonempty (V ⟶ U.obj e)

/-- 各段の Čech 脈体と、その射影を保つ遷移。 -/
structure ProCechNerveData (U : ℕ ⥤ C) where
  level : ∀ e : ℕ, CechNerveData (U.obj e)
  transition : ∀ e : ℕ, (level e).obj ⟶ (level (e + 1)).obj
  transition_proj : ∀ (e n : ℕ) (i : Fin (n + 1)),
    (transition e).app (Opposite.op ⦋n⦌) ≫ (level (e + 1)).proj n i =
      (level e).proj n i ≫ U.map (homOfLE (Nat.le_succ e))

/-- 段と単体の二重添字を持つ、環の向きの関手。 -/
def proCechIndexFunctor {U : ℕ ⥤ C} (d : ProCechNerveData U) :
    ℕᵒᵖ × SimplexCategory ⥤ Cᵒᵖ :=
  Functor.uncurry.obj ((Functor.ofSequence d.transition).op ⋙
    (Functor.leftOpRightOpEquiv SimplexCategory C).functor)

/-- 二重添字の対象は、指定された段の Čech 項。 -/
@[simp] theorem proCechIndexFunctor_obj {U : ℕ ⥤ C} (d : ProCechNerveData U)
    (e : ℕ) (n : SimplexCategory) :
    (proCechIndexFunctor d).obj (Opposite.op e, n) =
      Opposite.op ((d.level e).obj.obj (Opposite.op n)) := rfl

/-- 圏同値は塔の pro 弱終性を保つ。 -/
theorem IsProWeaklyTerminal.map_equivalence {D : Type u'} [Category.{v'} D]
    {U : ℕ ⥤ C} (hU : IsProWeaklyTerminal U) (e : C ≌ D) :
    IsProWeaklyTerminal (U ⋙ e.functor) := by
  intro V
  obtain ⟨n, ⟨f⟩⟩ := hU (e.inverse.obj V)
  exact ⟨n, ⟨(e.counitIso.app V).inv ≫ e.functor.map f⟩⟩

end CategoryTheory
