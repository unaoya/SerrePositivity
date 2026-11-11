module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveInvertedHom

/-!
概要：元の二単体の三辺に対する S-equivalence の二つから三つ目の性質。
方針：端点を持つ辺と元の一次単体を照合し、hX の合成則を適用する。
規約：余極限での閉性は別工程。使われ方：HTT 5.5.4.5(3) の強飽和性の一条件。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]
/-- 型付きの辺の S-equivalence と元の一次単体の所属条件は同値。 -/
lemma localEquivalenceHom_iff_edge_mem (W : Set (X _⦋1⦌)) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom W (SSet.Truncated.HomotopyCategory.homMk e) ↔
      e.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  constructor <;> intro h z hz
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isLocalForHom_homMk_iff_edgeOfSimplex e z).mp (h z hz)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isLocalForHom_homMk_iff_edgeOfSimplex e z).mpr (h z hz)

/-- S-equivalence の辺集合は全ての可逆辺を含む。 -/
lemma localEquivalences_mem_of_isInvertibleEdge (W : Set (X _⦋1⦌)) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    e.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) := he
  exact (localEquivalenceHom_iff_edge_mem W e).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom.of_isIso W _)

variable (W : Set (X _⦋1⦌)) {x y z : X _⦋0⦌}
  {e01 : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
  {e12 : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
  {e02 : SSet.Truncated.Edge (X := (truncation 2).obj X) x z}
  (t : SSet.Truncated.Edge.CompStruct e01 e12 e02)
include t in
/-- 元の二単体の短い二辺が S-equivalence なら長辺もそうである。 -/
lemma localEquivalences_compStruct (h01 : e01.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W)
    (h12 : e12.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W) : e02.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  apply (localEquivalenceHom_iff_edge_mem W e02).mp
  rw [← SSet.Truncated.HomotopyCategory.homMk_comp_homMk t]
  exact ((localEquivalenceHom_iff_edge_mem W e01).mpr h01).comp
    ((localEquivalenceHom_iff_edge_mem W e12).mpr h12)
include t in
/-- 元の二単体の先頭辺と長辺から最後の辺の S-equivalence を回収する。 -/
lemma localEquivalences_compStruct_cancel_left (h01 : e01.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W)
    (h02 : e02.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W) : e12.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  apply (localEquivalenceHom_iff_edge_mem W e12).mp
  apply ((localEquivalenceHom_iff_edge_mem W e01).mpr h01).cancel_left
  rw [SSet.Truncated.HomotopyCategory.homMk_comp_homMk t]
  exact (localEquivalenceHom_iff_edge_mem W e02).mpr h02
include t in
/-- 元の二単体の最後の辺と長辺から先頭辺の S-equivalence を回収する。 -/
lemma localEquivalences_compStruct_cancel_right (h12 : e12.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W)
    (h02 : e02.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W) : e01.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  apply (localEquivalenceHom_iff_edge_mem W e01).mp
  apply ((localEquivalenceHom_iff_edge_mem W e12).mpr h12).cancel_right
  rw [SSet.Truncated.HomotopyCategory.homMk_comp_homMk t]
  exact (localEquivalenceHom_iff_edge_mem W e02).mpr h02

end
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
