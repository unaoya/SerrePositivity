module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionBKIsLimit
public import SerrePositivity.KST.Spectra.SpectrumNativeCircleConeSection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEdgeIntervalCells

/-!
概要：元の評価錐から元の companion の極限錐への実際の辺と、その頂点の BF 自己射。
方針：元の同じ strict 図式の slice の終対象性で辺を取り、頂点と join 図式をそのまま読む。
規約：元の錐全体を保持し、頂点の射の可逆性を仮定しない。使われ方：符号による比較判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance companionConeComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の評価錐全体から、同じ図式上の元の companion 極限錐への実際の辺。 -/
def circleCompanionConeComparison (z : Sp.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val))).Edge
      (nativeCircleStrictCone z) (circleCompanionBKCoherentCone z) := by
  let e := Classical.choice
    ((circleCompanionBKCoherentCone_isLimit z).nonempty_edge (nativeCircleStrictCone z))
  exact SSet.Edge.mk e.edge e.src_eq e.tgt_eq

/-- 同じ辺の頂点方向を、元の円 cotensor の二つの標準頂点で表示する。 -/
def circleCompanionConeComparisonBFEdge (z : Sp.{u} _⦋0⦌) :
    Sp.{u}.Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val)) :=
  ((circleCompanionConeComparison z).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)))).ofEq
    (nativeCircleStrictCone_vertex z) (circleCompanionBKCoherentCone_vertex z)

/-- 元の錐の比較辺の apex にある、実際の BF 自己射。 -/
def circleCompanionConeComparisonHom (z : Sp.{u} _⦋0⦌) :
    cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val ⟶
      cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (circleCompanionConeComparisonBFEdge z)

/-- この BF 自己射の元の辺は、元の錐の比較の頂点への射影そのもの。 -/
lemma circleCompanionConeComparisonHom_edge (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleCompanionConeComparisonHom z) =
      circleCompanionConeComparisonBFEdge z := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom _

/-- 元の比較辺全体が表す、元の底の図式上の join 図式。 -/
def circleCompanionConeComparisonExtension (z : Sp.{u} _⦋0⦌) :=
  (circleCompanionConeComparison z).edge.val

/-- 元の比較辺の底への制限は、元の strict な cospan 図式全体。 -/
lemma circleCompanionConeComparisonExtension_base (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u + 1}) _ ≫ circleCompanionConeComparisonExtension z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
        (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val) :=
  (circleCompanionConeComparison z).edge.property

/-- 元の比較辺の始点は、元の評価錐全体そのもの。 -/
lemma circleCompanionConeComparisonExtension_source (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 _) ≫ circleCompanionConeComparisonExtension z =
      (nativeCircleStrictCone z).val :=
  congrArg Subtype.val (circleCompanionConeComparison z).src_eq

/-- 元の比較辺の終点は、元の companion 錐全体そのもの。 -/
lemma circleCompanionConeComparisonExtension_target (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 _) ≫ circleCompanionConeComparisonExtension z =
      (circleCompanionBKCoherentCone z).val :=
  congrArg Subtype.val (circleCompanionConeComparison z).tgt_eq

/-- 元の比較辺の apex への制限は、指定した BF 自己射の元の辺。 -/
lemma circleCompanionConeComparisonExtension_apex (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u + 1}) _ ≫ circleCompanionConeComparisonExtension z =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleCompanionConeComparisonHom z)).edge := by
  rw [circleCompanionConeComparisonHom_edge]
  change _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv _)
  rw [Equiv.symm_apply_apply]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
