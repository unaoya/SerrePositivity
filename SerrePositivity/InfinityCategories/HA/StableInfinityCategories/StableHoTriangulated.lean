module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableHoClosure

/-! # 実安定閉包の三角的対象条件

概要：実安定閉包は h C 上で全整数シフトに閉じた三角的対象条件となる。
方針：可縮三角形の回転と三角閉性から正負一回シフトを得て整数帰納する。
規約：有限和や retract を閉包の定義に加えない。使われ方：Verdier 分数計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory Limits Pretriangulated SSet
open scoped _root_.Simplicial
section ShiftClosure
variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [P.IsTriangulatedClosed₁] [P.IsTriangulatedClosed₃]

omit [P.IsTriangulatedClosed₁] in
/-- 零を含み三角形の第三項で閉じる対象条件は正一回シフトで閉じる。 -/
lemma triangulatedClosed_shift_one {a : C} (ha : P a) : P (a⟦(1 : ℤ)⟧) := by
  exact P.ext_of_isTriangulatedClosed₃ (contractibleTriangle a).rotate
    (rot_of_distTriang _ (contractible_distinguished a)) ha P.prop_zero

omit [P.IsTriangulatedClosed₃] in
/-- 零を含み三角形の第一項で閉じる対象条件は負一回シフトで閉じる。 -/
lemma triangulatedClosed_shift_neg_one {a : C} (ha : P a) : P (a⟦(-1 : ℤ)⟧) := by
  have h : P ((a⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) :=
    P.prop_of_iso ((shiftFunctorCompIsoId C (-1 : ℤ) 1 (by decide)).app a).symm ha
  exact P.ext_of_isTriangulatedClosed₁ (contractibleTriangle (a⟦(-1 : ℤ)⟧)).rotate
    (rot_of_distTriang _ (contractible_distinguished _)) P.prop_zero h

/-- 零を含み三角形の第一項・第三項で閉じる対象条件は全整数シフトで閉じる。 -/
lemma triangulatedClosed_shift (n : ℤ) {a : C} (ha : P a) : P (a⟦n⟧) := by
  induction n using Int.induction_on with
  | zero => exact P.prop_of_iso ((shiftFunctorZero C ℤ).app a).symm ha
  | succ n ih =>
    exact P.prop_of_iso ((shiftFunctorAdd C (n : ℤ) 1).app a).symm
      (triangulatedClosed_shift_one P ih)
  | pred n ih =>
    exact P.prop_of_iso
      ((shiftFunctorAdd' C (-(n : ℤ)) (-1) (-(n : ℤ) - 1) (by omega)).app a).symm
      (triangulatedClosed_shift_neg_one P ih)
end ShiftClosure

variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 実安定閉包の対象条件は全整数シフトで閉じる。 -/
lemma stableHoClosure_shift (P : Set (X _⦋0⦌)) (n : ℤ) {a : hoFunctor.obj X}
    (ha : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P a) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P (a⟦n⟧) :=
  triangulatedClosed_shift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P) n ha

/-- h C の実安定閉包は三角的対象条件。 -/
instance stableHoClosure_isTriangulated (P : Set (X _⦋0⦌)) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).IsTriangulated where
  isStableUnderShiftBy n := ⟨fun _ ha => stableHoClosure_shift P n ha⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
