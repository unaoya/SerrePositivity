module
public import SerrePositivity.KST.SConstruction.FunctorStability
public import SerrePositivity.KST.SConstruction.TrivialFibrationStability
public import SerrePositivity.KST.SConstruction.IteratedObjects

/-! # S 構成と有限反復の安定性
概要：安定な quasicategory の S_n とその有限反復は安定。
方針：第一行の関手圏の安定性を trivial Kan fibration で反映する。
規約：α-S の安定性の定義をそのまま使う。使われ方：反復 S• の構造。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：S_n は安定な quasicategory を安定な quasicategory へ送る。
方針：第一行制限で関手圏の安定性を源へ反映する。
規約：n = 0 も含む。使われ方：S 構成の反復。 -/
instance sConstruction_isStable (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (sConstruction n C) :=
  isStable_of_trivialKanFibration (firstRowRestriction n C)

/-- 概要：S 構成の任意の有限反復は安定な quasicategory。
方針：反復の長さについて帰納する。
規約：空リストは元の C。使われ方：多単体的 K 理論の各対象。 -/
instance iteratedSConstruction_isStable (ns : List ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (iteratedSConstruction ns C) := by
  induction ns with
  | nil => exact inferInstanceAs (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C)
  | cons n ns ih =>
    let := ih
    exact inferInstanceAs (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (sConstruction n (iteratedSConstruction ns C)))

end SerrePositivity.KST.SConstruction
