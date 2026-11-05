module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Stable.Infinity
open SerrePositivity.KST.LocalizingInvariants

/-- 完全関手が定める元の coherent nerve の辺。 -/
def stableArrow {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) :
    _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex A) (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex B) :=
  coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) F

/-- 安定対象間の辺は、元の完全関手と一対一に対応する。 -/
def stableArrowEquiv (A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex A) (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex B) ≃ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B :=
  coherentNerveEdgeEquiv (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) A B

lemma stableArrowEquiv_arrow {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) :
    _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrowEquiv A B (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow F) = F :=
  coherentNerveEdgeToHom_edge (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) F

/-- 零の安定圏では全ての実頂点が零対象。 -/
def IsZeroCategory (A : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}) : Prop :=
  ∀ a : A.obj _⦋0⦌, IsZeroVertex a

/-- A → B → C の零合成を保持した coherent 四角形の提示。 -/
structure VerdierDiagram extends _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.{u} where
  square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}
  left_eq : squareVertex square 0 0 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex left
  middle_eq : squareVertex square 1 0 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex middle
  right_eq : squareVertex square 1 1 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex right
  bottom_edge : squareBottomEdge ≫ square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow inclusion).edge
  right_edge : squareRightEdge ≫ square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow projection).edge
  zero_corner : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableObject (squareVertex square 0 1))

end SerrePositivity.InfinityCategories.Stable.Infinity

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.IsZeroCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsZeroCategory := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.IsZeroCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableArrow := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrowEquiv (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableArrowEquiv := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrowEquiv

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableArrowEquiv_arrow := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrowEquiv_arrow

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram._sizeOf_inst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.bottom_edge := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.bottom_edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.left_eq := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.left_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.middle_eq := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.middle_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.mk := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.rec := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.right_edge := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.right_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.right_eq := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.right_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.square (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.square := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.square

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.toVerdierSequence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.toVerdierSequence := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.toVerdierSequence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.zero_corner := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.zero_corner

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.mk.sizeOf_spec
