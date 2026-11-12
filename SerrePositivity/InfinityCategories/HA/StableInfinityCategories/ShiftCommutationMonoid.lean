module
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-! # シフト交換同型の次数付きモノイド

概要：関手と一つのシフトとの交換同型を、次数を含めて合成する。
方針：Mathlib の交換同型の加法・単位・結合則を依存和のモノイドへまとめる。
規約：整数シフトの交換同型の全整合条件を後に構成するための補助表現。
使われ方：S6 の一回の懸垂比較から全整数シフトへの延長。
-/
@[expose] public section
noncomputable section
universe v u v' u'
open CategoryTheory
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D)

/-- 概要：次数 n における関手とシフトの交換同型。
方針：左右のシフトの後に同じ関手を合成する。
規約：Mathlib の CommShift の向き。使われ方：次数付き合成。 -/
abbrev StableShiftCommutationIso (n : ℤ) :=
  shiftFunctor C n ⋙ F ≅ F ⋙ shiftFunctor D n

/-- 概要：次数とその次数の交換同型を束ねる。
方針：整数を底とする依存和を使う。
規約：次数零の単位と次数の加法に沿う乗法。使われ方：整数冪の構成。 -/
def StableShiftCommutation := Σ n : ℤ, StableShiftCommutationIso F n

/-- 概要：等式で添字を指定した交換同型の合成は通常の合成と同じ。
方針：次数の等式で帰納する。
規約：異なる添字を HEq で比較する。使われ方：依存和の結合則。 -/
lemma stableShiftCommutationIsoAdd_heq {a b c : ℤ} (h : a + b = c)
    (ea : StableShiftCommutationIso F a) (eb : StableShiftCommutationIso F b) :
    HEq (Functor.CommShift.isoAdd ea eb) (Functor.CommShift.isoAdd' h ea eb) := by
  subst c
  rfl

/-- 概要：全次数の交換同型は合成に関してモノイドをなす。
方針：Mathlib の交換同型の単位・結合則を HEq を通して依存和へ移す。
規約：左右の順序は次数の加法の順序。使われ方：一回の比較の整数冪。 -/
instance stableShiftCommutation_monoid : Monoid (StableShiftCommutation F) where
  one := ⟨0, Functor.CommShift.isoZero F ℤ⟩
  mul a b := ⟨a.1 + b.1, Functor.CommShift.isoAdd a.2 b.2⟩
  one_mul a := by
    apply Sigma.ext (zero_add a.1)
    exact (stableShiftCommutationIsoAdd_heq F (zero_add a.1) _ _).trans
      (heq_of_eq (Functor.CommShift.isoZero_isoAdd'_ a.2))
  mul_one a := by
    apply Sigma.ext (add_zero a.1)
    exact (stableShiftCommutationIsoAdd_heq F (add_zero a.1) _ _).trans
      (heq_of_eq (Functor.CommShift.isoAdd'_isoZero a.2))
  mul_assoc a b c := by
    apply Sigma.ext (add_assoc a.1 b.1 c.1)
    exact (stableShiftCommutationIsoAdd_heq F (add_assoc a.1 b.1 c.1) _ _).trans
      (heq_of_eq (Functor.CommShift.isoAdd'_assoc a.2 b.2 c.2 rfl rfl
        (add_assoc a.1 b.1 c.1)))

/-- 概要：交換同型の次数は積を和へ送る。
方針：依存和の第一成分を取る。
規約：加法群 ℤ の乗法表示へのモノイド準同型。使われ方：整数冪の次数の計算。 -/
def stableShiftCommutationDegree : StableShiftCommutation F →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd a.1
  map_one' := rfl
  map_mul' _ _ := rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
