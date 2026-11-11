module
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Endomorphism

/-! # 厳密な自己同型の整数シフト

概要：圏の厳密な自己同型の整数冪から整合的な整数シフトを作る。
方針：Aut の群構造の整数冪の等式を関手の等式に移す。
規約：この補助構成では単位・合成の同型は等号から得る。
使われ方：S4 の suspension 自己同値からの HasShift の構成。
-/
@[expose] public section
noncomputable section
universe v u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：加法に関して厳密に合成する関手の族からシフトの整合データを得る。
方針：全ての構造同型を等号による同型にし、輸送の合成則で整合性を証明する。
規約：任意の加法モノイド。使われ方：厳密な整数冪のシフト。 -/
def stableStrictShiftMkCore {C : Type u} [Category.{v} C] {A : Type*} [AddMonoid A]
    (F : A → C ⥤ C) (h₀ : F 0 = 𝟭 C) (hadd : ∀ n m, F (n + m) = F n ⋙ F m) :
    ShiftMkCore C A where
  F := F
  zero := eqToIso h₀
  add n m := eqToIso (hadd n m)
  assoc_hom_app m₁ m₂ m₃ X := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans]
  zero_add_hom_app n X := by
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]
  add_zero_hom_app n X := by
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans]

/-- 概要：圏の自己同型の整数冪を通常の自己関手の族にする。
方針：Aut の整数冪の順方向の関手を取る。
規約：Aut の乗法と関手の合成の順序に注意する。使われ方：整数シフトの族。 -/
def stableAutPowerFunctor {C : Type u} [Category.{v} C] (e : Aut (Cat.of C)) (n : ℤ) : C ⥤ C :=
  (e ^ n).asIso.hom.toFunctor

/-- 概要：整数冪の零番目の関手は恒等関手。
方針：群の零乗の式。規約：厳密な等号。使われ方：シフトの単位。 -/
lemma stableAutPowerFunctor_zero {C : Type u} [Category.{v} C] (e : Aut (Cat.of C)) :
    stableAutPowerFunctor e 0 = 𝟭 C := by
  simp only [stableAutPowerFunctor, zpow_zero]
  rfl

/-- 概要：整数冪の和は二つの関手の合成になる。
方針：Aut の乗法の逆順を整数の加法の可換性で合わせる。
規約：厳密な関手の等号。使われ方：シフトの合成。 -/
lemma stableAutPowerFunctor_add {C : Type u} [Category.{v} C] (e : Aut (Cat.of C)) (n m : ℤ) :
    stableAutPowerFunctor e (n + m) = stableAutPowerFunctor e n ⋙ stableAutPowerFunctor e m := by
  have h : e ^ (n + m) = e ^ m * e ^ n := by rw [← zpow_add, add_comm]
  dsimp only [stableAutPowerFunctor]
  rw [h]
  rfl

/-- 概要：厳密な自己同型から整数シフトを作る。
方針：整数冪の単位と合成の等式から ShiftMkCore を作る。
規約：全ての整合条件を含む HasShift。使われ方：skeleton 上の補助シフト。 -/
@[instance_reducible]
def stableAutHasShift {C : Type u} [Category.{v} C] (e : Aut (Cat.of C)) : HasShift C ℤ :=
  hasShiftMk C ℤ (stableStrictShiftMkCore (stableAutPowerFunctor e)
    (stableAutPowerFunctor_zero e) (stableAutPowerFunctor_add e))

/-- 概要：構成したシフトは指定した自己同型の整数冪そのもの。
方針：HasShift の構成の定義を計算する。
規約：局所的に構成したシフトを用いる。使われ方：一回シフトと元の関手の照合。 -/
lemma stableAutHasShift_shiftFunctor {C : Type u} [Category.{v} C] (e : Aut (Cat.of C)) (n : ℤ) :
    letI := stableAutHasShift e
    shiftFunctor C n = stableAutPowerFunctor e n := rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
