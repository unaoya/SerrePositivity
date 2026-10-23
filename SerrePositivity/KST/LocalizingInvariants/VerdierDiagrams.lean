module

public import SerrePositivity.KST.LocalizingInvariants.StableInfinity
public import SerrePositivity.KST.LocalizingInvariants.VerdierSequence
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv

/-!
概要：実際の coherent 四角形として提示した抽象 Verdier 列。
方針：抽象列の包含・商を二辺として固定し、第四の安定圏の全対象の零性を記録する。
規約：この提示の存在は別の定理。使われ方：Sp 値関手による fiber 列の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 完全関手が定める元の coherent nerve の辺。 -/
def stableArrow {A B : StableCategory.{u}} (F : ExactMap A B) :
    StableInfinity.{u}.Edge (stableVertex A) (stableVertex B) :=
  coherentNerveEdge (C := StableQCat.{u}) F

/-- 安定対象間の辺は、元の完全関手と一対一に対応する。 -/
def stableArrowEquiv (A B : StableCategory.{u}) :
    StableInfinity.{u}.Edge (stableVertex A) (stableVertex B) ≃ ExactMap A B :=
  coherentNerveEdgeEquiv (C := StableQCat.{u}) A B

lemma stableArrowEquiv_arrow {A B : StableCategory.{u}} (F : ExactMap A B) :
    stableArrowEquiv A B (stableArrow F) = F :=
  coherentNerveEdgeToHom_edge (C := StableQCat.{u}) F

/-- 零の安定圏では全ての実頂点が零対象。 -/
def IsZeroCategory (A : StableCategory.{u}) : Prop :=
  ∀ a : A.obj _⦋0⦌, IsZeroVertex a

/-- A → B → C の零合成を保持した coherent 四角形の提示。 -/
structure VerdierDiagram extends VerdierSequence.{u} where
  square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u}
  left_eq : squareVertex square 0 0 = stableVertex left
  middle_eq : squareVertex square 1 0 = stableVertex middle
  right_eq : squareVertex square 1 1 = stableVertex right
  bottom_edge : squareBottomEdge ≫ square = SSet.yonedaEquiv.symm (stableArrow inclusion).edge
  right_edge : squareRightEdge ≫ square = SSet.yonedaEquiv.symm (stableArrow projection).edge
  zero_corner : IsZeroCategory (stableObject (squareVertex square 0 1))

end SerrePositivity.KST.LocalizingInvariants
