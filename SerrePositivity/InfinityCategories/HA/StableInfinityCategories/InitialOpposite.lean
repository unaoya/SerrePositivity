module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.BoundaryOpposite

/-! # 始対象と終対象の反転

概要：始対象性と反転した単体集合の終対象性は同値である。
方針：境界と端点を反転し、充填を二重反転の同型で戻す。
規約：quasicategory 性は不要。使われ方：相対始対象と相対終対象の双対化。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：零頂点を反転しても零頂点である。
方針：始対象性と終対象性を交換する。
規約：頂点は opObjEquiv で移す。使われ方：suspension と loop の双対性。 -/
lemma IsZeroVertex.op {X : SSet.{u}} {x : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := X.op) (SSet.opObjEquiv.symm x) :=
  ⟨hx.2.op_isInitialVertex, hx.1.op_isTerminalVertex⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroVertex (op)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
