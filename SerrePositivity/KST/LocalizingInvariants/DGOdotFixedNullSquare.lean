module

public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullSquare
public import SerrePositivity.KST.SConstruction.DGOdotVerdierInput

/-!
概要：K-S• の元の比較対角と指定実商射を保つ、固定 S 内の零化四角形。
方針：元の商の同じ ε を全対象商からの延長に指定し、一般の固定 S 構成へ渡す。
規約：dg 自然収縮・長方形全体・零角の Perf 値の零性は仮定済み成果としない。
使われ方：Sp-6 の具体的対角商と相対 Verdier 接続。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.LocalizingInvariants

variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 元の対角後の商合成に、元の像対象の指定 ε をそのまま付ける。 -/
def dgOdotCompositeContracted :
    DGQuotient.ContractedFunctor R (dgOdotDiagonalSourceInput R d) Set.univ
      (dgOdotQuotientInputVertex R d) where
  toDGFunctor := (dgOdotDiagonalInputMap R d).down.comp (dgOdotProjectionInputMap R d).down
  homotopy a := pointedDGQuotientDiagonalEpsilon R (dgOdotQuotientInput R d).diagonal
    a.val.label.down
  d_homotopy a := pointedDGQuotientDiagonalEpsilon_d R (dgOdotQuotientInput R d).diagonal
    a.val.label.down

/-- 元の dg 対角始域の全対象商を、同じ固定 S の零角候補にする。 -/
abbrev dgOdotNullInput := dgFixedNullInput R (dgOdotDiagonalSourceInput R d)

/-- 元の包含・実商射を全一単体として固定した、S 内の実零化四角形。 -/
lemma exists_dgOdotFixedNullSquare :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotDiagonalInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotProjectionInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotDiagonalSourceInput R d))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgOdotCompositeContracted R d))).edge :=
  exists_dgFixedNullSquare R (dgOdotDiagonalInputMap R d) (dgOdotProjectionInputMap R d)
    (dgOdotCompositeContracted R d) rfl

/-- D の Verdier 証拠と零角の Perf 値の零性を、元の対角商の相対提示へ接続する。 -/
lemma exists_dgOdotRelativeNullDiagram (h : DGOdotVerdierInput R d)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R (dgOdotNullInput R d))) :
    ∃ t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, u + 1} R),
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d) ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotGluingInput R d) ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotQuotientInputVertex R d) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotDiagonalInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.square =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotProjectionInputMap R d)).edge :=
  exists_dgFixedNullRelativeRoof R (dgOdotDiagonalInputMap R d) (dgOdotProjectionInputMap R d)
    (dgOdotCompositeContracted R d) rfl h.isVerdier hz

end SerrePositivity.KST.LocalizingInvariants
