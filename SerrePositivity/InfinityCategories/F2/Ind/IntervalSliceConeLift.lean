module

public import SerrePositivity.InfinityCategories.Stable.JoinAssociatorBoundary
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-!
概要：区間図式への全錐を、その終点の slice 内の始点余錐として読む。
方針：区間を二点の join として展開し、join の結合同型で組み替えて curry する。
規約：元の全錐と始点制限を保持。使われ方：元の円柱の始点上の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X : SSet.{u}} (d : (Δ[1] : SSet.{u}) ⟶ X) (f : A ⟶ sliceOver d)

/-- 区間への全錐を、同じ終点を持つ二重の右余錐へ組み替える。 -/
def intervalSliceConeReassociation : join (join A (Δ[0] : SSet.{u})) Δ[0] ⟶ X :=
  (stableJoinAssociator A Δ[0] Δ[0]).hom ≫
    joinMap (𝟙 A) (joinStdSimplexIso 0 0).hom ≫ sliceOverUncurry f

/-- 組み替えた全錐の最後の点は、元の区間の同じ終点。 -/
lemma intervalSliceConeReassociation_fixed :
    joinInr (join A (Δ[0] : SSet.{u})) Δ[0] ≫ intervalSliceConeReassociation d f =
      stdSimplex.δ 0 ≫ d := by
  rw [intervalSliceConeReassociation, ← Category.assoc, stableJoinAssociator_inr,
    Category.assoc, ← Category.assoc (joinInr A _), joinInr_joinMap,
    Category.assoc, sliceOverUncurry_fixed, ← Category.assoc,
    joinStdSimplexIso_zero_inr]

/-- 区間の終点の slice 内で、元の始点余錐全体を持ち上げる。 -/
def intervalSliceConeLift : join A (Δ[0] : SSet.{u}) ⟶ sliceOver (stdSimplex.δ 0 ≫ d) :=
  sliceOverCurry (intervalSliceConeReassociation d f) (intervalSliceConeReassociation_fixed d f)

/-- 持ち上げた全余錐を読み戻すと、元の全錐の組み替えそのもの。 -/
lemma intervalSliceConeLift_uncurry :
    sliceOverUncurry (intervalSliceConeLift d f) = intervalSliceConeReassociation d f :=
  sliceOverUncurry_curry _ _

/-- slice への持ち上げは、元の区間の始点制限の全余錐を厳密に被覆する。 -/
lemma intervalSliceConeLift_projection :
    intervalSliceConeLift d f ≫ sliceOverProjection (stdSimplex.δ 0 ≫ d) =
      sliceOverUncurry (f ≫ sliceOverRestrict d (stdSimplex.δ 1)) := by
  rw [intervalSliceConeLift, sliceOverCurry_projection, intervalSliceConeReassociation,
    ← Category.assoc, stableJoinAssociator_inl, ← Category.assoc, ← joinMap_comp,
    Category.id_comp, joinStdSimplexIso_zero_inl, sliceOverUncurry_restrict]

end SerrePositivity.InfinityCategories.F2.Ind
