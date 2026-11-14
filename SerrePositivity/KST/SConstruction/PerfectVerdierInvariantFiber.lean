module
public import SerrePositivity.KST.SConstruction.PerfectVerdierPresentation
public import SerrePositivity.KST.SConstruction.PerfectLocalizingInvariant

/-! # 任意の Cat^perf の実提示列の不変量値 fiber 列
概要：任意の実商と完備化の列を、同じ対象・二辺を持つ Sp の実 fiber 列へ送る。
方針：証明済みの coherent 提示を、元の局所化不変量の同じ単体的写像で写す。
規約：群ごとの核・余核で代用しない。使われ方：Tamme と BGT (a) の局所化性の界面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {E : perfectStableInfinity.{u} ⟶ Sp.{u}} (hE : IsPerfectLocalizingInvariant E)

/-- 任意の元の実提示列を、同じ coherent 四角形の像の三角形へ送る。 -/
def IsPerfectLocalizingInvariant.sequenceFiberTriangle (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u} := hE.fiberTriangle d.presentation

/-- 図式の存在を追加入力にせず、元の全提示列に実 fiber 列を得る。 -/
lemma IsPerfectLocalizingInvariant.sequenceFiberTriangle_isFiber
    (d : PerfectVerdierSequence.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence (hE.sequenceFiberTriangle d) :=
  hE.fiberTriangle_isFiber d.presentation

/-- 同じ実 fiber 列の左端は、元の左安定圏の同じ不変量値。 -/
lemma IsPerfectLocalizingInvariant.sequenceFiberTriangle_left
    (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (hE.sequenceFiberTriangle d).square 0 0 =
      E.app (Opposite.op ⦋0⦌) d.leftVertex := by
  change E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.presentation.square 0 0) = _
  exact congrArg (fun x => E.app (Opposite.op ⦋0⦌) x) (perfectVerdierSquare_vertices d).1

/-- 同じ実 fiber 列の中央は、元の中央安定圏の同じ不変量値。 -/
lemma IsPerfectLocalizingInvariant.sequenceFiberTriangle_middle
    (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (hE.sequenceFiberTriangle d).square 1 0 =
      E.app (Opposite.op ⦋0⦌) d.middleVertex := by
  change E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.presentation.square 1 0) = _
  exact congrArg (fun x => E.app (Opposite.op ⦋0⦌) x) (perfectVerdierSquare_vertices d).2.1

/-- 同じ実 fiber 列の右端は、商の冪等完備化の同じ不変量値。 -/
lemma IsPerfectLocalizingInvariant.sequenceFiberTriangle_right
    (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (hE.sequenceFiberTriangle d).square 1 1 =
      E.app (Opposite.op ⦋0⦌) d.rightVertex := by
  change E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.presentation.square 1 1) = _
  exact congrArg (fun x => E.app (Opposite.op ⦋0⦌) x) (perfectVerdierSquare_vertices d).2.2

/-- 値域の包含辺は、元の包含を表す同じ Cat^perf 辺の不変量による像。 -/
lemma IsPerfectLocalizingInvariant.sequenceFiberTriangle_bottom
    (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (hE.sequenceFiberTriangle d).square =
      SSet.yonedaEquiv.symm
        ((perfectStableArrow d.verdier.inclusion d.left_complete
          d.middle_complete).map E).edge := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (d.presentation.square ≫ E) = _
  rw [← Category.assoc, d.presentation_bottom, SSet.yonedaEquiv_symm_comp]
  rfl

/-- 値域の右辺は、完備化後の元の右射を表す同じ Cat^perf 辺の像。 -/
lemma IsPerfectLocalizingInvariant.sequenceFiberTriangle_projection
    (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (hE.sequenceFiberTriangle d).square =
      SSet.yonedaEquiv.symm
        ((perfectStableArrow d.projection d.middle_complete d.right_complete).map E).edge := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (d.presentation.square ≫ E) = _
  rw [← Category.assoc, d.presentation_right, SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.KST.SConstruction
