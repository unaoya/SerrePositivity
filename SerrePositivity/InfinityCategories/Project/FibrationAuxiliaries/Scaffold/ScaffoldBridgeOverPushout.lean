module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldNerveBridge

/-!
概要：最初の区間と尾部単体を、任意の底上の同じ pushout として表示する。
方針：元の pushout の二射と共有頂点を、その底への射と合成する。
規約：標準区間と元の尾部の nerve を使う。
使われ方：高次単体の元の Hom の二成分 Segal 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold
namespace ScaffoldBridgeOver

variable (n : ℕ) {B : SSet.{u}}
  (h : pushout (stdSimplex.δ (0 : Fin 2))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ⟶ B)

/-- 最初の区間と尾部を貼った元の空間。 -/
def apex : Over B := Over.mk h

/-- 元の最初の区間。 -/
def first : Over B := Over.mk (pushout.inl _ _ ≫ h)

/-- 元の尾部単体。 -/
def tail : Over B := Over.mk (pushout.inr _ _ ≫ h)

/-- 区間の終点と尾部の始点として共有する同じ頂点。 -/
def vertex : Over B := Over.mk (stdSimplex.δ (0 : Fin 2) ≫ pushout.inl _ _ ≫ h)

/-- 共有頂点の最初の区間への包含。 -/
def toFirst : vertex n h ⟶ first n h := Over.homMk (stdSimplex.δ (0 : Fin 2)) rfl

/-- 共有頂点の尾部への包含。 -/
def toTail : vertex n h ⟶ tail n h :=
  Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) (by
    change _ ≫ (pushout.inr _ _ ≫ h) = _ ≫ (pushout.inl _ _ ≫ h)
    rw [← Category.assoc, ← Category.assoc, pushout.condition])

/-- 最初の区間の元の包含。 -/
def firstInclusion : first n h ⟶ apex n h := Over.homMk (pushout.inl _ _) rfl

/-- 尾部単体の元の包含。 -/
def tailInclusion : tail n h ⟶ apex n h := Over.homMk (pushout.inr _ _) rfl

/-- 同じ四つの底上の射の基礎は、元の pushout をなす。 -/
lemma isPushout : IsPushout (toFirst n h).left (toTail n h).left
    (firstInclusion n h).left (tailInclusion n h).left := IsPushout.of_hasPushout _ _

instance : Mono (toTail n h).left := by
  change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _))
  infer_instance

end ScaffoldBridgeOver
end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold
