module
public import SerrePositivity.InfinityCategories.Stable.UniverseBoundaryFilling
public import SerrePositivity.InfinityCategories.Stable.Pointed

/-! # 始対象・終対象・零対象の宇宙比較

概要：実境界充填による始・終対象性と零対象性は ULift で保ち反映される。
方針：全正次元の最初／最後の頂点を固定した境界充填の同値を使う。
規約：quasicategory 性は不要。使われ方：普遍錐と安定性の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 実終対象性は宇宙持ち上げで保ち反映される。 -/
lemma isTerminalVertex_iff_ulift {X : SSet.{u}} (x : X _⦋0⦌) :
    IsTerminalVertex x ↔
      IsTerminalVertex (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) :=
  uliftBoundary_filling_at_vertex_iff x (fun n => Fin.last (n + 1))

/-- 実始対象性は宇宙持ち上げで保ち反映される。 -/
lemma isInitialVertex_iff_ulift {X : SSet.{u}} (x : X _⦋0⦌) :
    IsInitialVertex x ↔
      IsInitialVertex (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) :=
  uliftBoundary_filling_at_vertex_iff x (fun _ => 0)

/-- 実零対象性は同じ頂点の宇宙持ち上げで保ち反映される。 -/
lemma isZeroVertex_iff_ulift {X : SSet.{u}} (x : X _⦋0⦌) :
    IsZeroVertex x ↔
      IsZeroVertex (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) :=
  and_congr (isInitialVertex_iff_ulift x) (isTerminalVertex_iff_ulift x)

/-- 実零対象の存在は宇宙持ち上げで保ち反映される。 -/
lemma hasZeroVertex_iff_ulift (X : SSet.{u}) :
    HasZeroVertex X ↔ HasZeroVertex ((SSet.uliftFunctor.{v, u}).obj X) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨ULift.up x, (isZeroVertex_iff_ulift x).1 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x.down, (isZeroVertex_iff_ulift x.down).2 hx⟩

end SerrePositivity.InfinityCategories
