module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerSquareFixedSpanInitial
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberBaseChange

/-!
概要：固定 span の余錐比較から suspension の普遍四角形と厳密切断を構成する。
方針：実 fiber の同型で始対象性を余極限性へ戻し、全境界持ち上げを使う。
規約：安定性・有限余極限は仮定しない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
def zeroCornerSquareSpanPullbackIso (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquares X ≅
    pullback ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterSpanVertex).ι := by
  let P := fun v ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterSpanVertex
    (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X).app (Opposite.op ⦋0⦌) v)
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (Iso.refl _) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex P ?_ ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneInputFullSubcomplexIso _ _
  intro v
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanVertex_square_iff v).symm

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma zeroCornerSquareSpanPullbackIso_diagram (X : SSet.{u}) :
    (zeroCornerSquareSpanPullbackIso X).hom ≫
      pullback.fst ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterSpanVertex).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex).ι := by
  dsimp only [zeroCornerSquareSpanPullbackIso, Iso.trans_hom]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneInputFullSubcomplexIso_hom_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso_hom_ι]
  exact Category.comp_id _

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma zeroCornerSquareSpanPullbackIso_span (X : SSet.{u}) :
    (zeroCornerSquareSpanPullbackIso X).hom ≫
      pullback.snd ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterSpanVertex).ι = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterSpanVertex).ι).1
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    zeroCornerSquareSpanPullbackIso_diagram]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _).symm

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
def zeroCornerSquareFixedSpanRawIso (X : SSet.{u}) (b : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpans X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X) b ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X) b.val := by
  let q := pullback.snd ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterSpanVertex).ι
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X) q
    (zeroCornerSquareSpanPullbackIso X).hom (zeroCornerSquareSpanPullbackIso_span X) b
  have : IsIso f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberMap_isIso _ _ _ _ _
  exact asIso f ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterSpanVertex).ι b
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
