module
public import SerrePositivity.KST.SConstruction.PerfectVerdierSquareLift
public import SerrePositivity.KST.SConstruction.PerfectStableArrow

/-! # 任意の実 Verdier 提示から Cat^perf の coherent 図式へ
概要：元の包含・完備化後の右射と零角を保持する実図式を、任意の提示列から作る。
方針：同じ安定圏値四角形の Cat^perf への持ち上げと、四頂点の厳密な式を束ねる。
規約：図式の存在を追加入力にしない。使われ方：局所化不変量による全提示列の fiber 性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 全頂点を保つ持ち上げは、同じ元の三つの非零角を厳密に回収する。 -/
lemma perfectVerdierSquare_vertices (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (perfectVerdierSquare d) 0 0 = d.leftVertex ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (perfectVerdierSquare d) 1 0 = d.middleVertex ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (perfectVerdierSquare d) 1 1 = d.rightVertex := by
  have h := perfectVerdierRawSquare_vertices d
  constructor
  · apply Subtype.ext
    exact h.1
  constructor
  · apply Subtype.ext
    exact h.2.1
  · apply Subtype.ext
    exact h.2.2.1

/-- 任意の実提示列は、同じ元の右射を保つ Cat^perf の coherent 図式を持つ。 -/
def PerfectVerdierSequence.presentation (d : PerfectVerdierSequence.{u}) :
    PerfectVerdierDiagram.{u} where
  toPerfectVerdierSequence := d
  square := perfectVerdierSquare d
  left_eq := (perfectVerdierSquare_vertices d).1
  middle_eq := (perfectVerdierSquare_vertices d).2.1
  right_eq := (perfectVerdierSquare_vertices d).2.2
  bottom_edge := (congrArg (fun Q => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q)
    (perfectVerdierSquare_inclusion d)).trans (perfectVerdierRawSquare_edges d).1
  right_edge := (congrArg (fun Q => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q)
    (perfectVerdierSquare_inclusion d)).trans (perfectVerdierRawSquare_edges d).2.2.2
  zero_corner := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (perfectVerdierRawSquare d) 0 1))
    rw [(perfectVerdierRawSquare_vertices d).2.2.2, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero

/-- 同じ coherent 提示は、元の実商と冪等完備化を持つ列そのものを保持する。 -/
lemma PerfectVerdierSequence.presentation_sequence (d : PerfectVerdierSequence.{u}) :
    d.presentation.toPerfectVerdierSequence = d := rfl

/-- 同じ図式の包含辺は、Cat^perf の元の完全関手の実辺。 -/
lemma PerfectVerdierSequence.presentation_bottom (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.presentation.square =
      SSet.yonedaEquiv.symm
        (perfectStableArrow d.verdier.inclusion d.left_complete d.middle_complete).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  exact (Category.assoc _ _ _).trans
    (d.presentation.bottom_edge.trans
      (perfectStableArrow_inclusion d.verdier.inclusion d.left_complete d.middle_complete).symm)

/-- 同じ図式の右辺は、完備化後の元の完全関手の実辺。 -/
lemma PerfectVerdierSequence.presentation_right (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.presentation.square =
      SSet.yonedaEquiv.symm
        (perfectStableArrow d.projection d.middle_complete d.right_complete).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  exact (Category.assoc _ _ _).trans
    (d.presentation.right_edge.trans
      (perfectStableArrow_inclusion d.projection d.middle_complete d.right_complete).symm)

end SerrePositivity.KST.SConstruction
