module
public import SerrePositivity.KST.Fibration.VerdierZeroCornerMap
public import SerrePositivity.KST.Fibration.VerdierNullCompositeComparison
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSMap

/-!
概要：指定 Verdier 上側二胞体の実二短辺と、同じ全 S• 零値作用の合成。
方針：元の上辺を回収し、対象等号だけに沿って元の合成 path を輸送する。
規約：指定した二胞体・左右の実完全射を選び直さない。
使われ方：商核上辺と指定零角を経由する上側合成の全比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の指定 coherent 上辺から回収する、同じ零角から右端への完全射。 -/
def verdierTopExactMap (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 1)) d.right :=
  exactMapTransport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj d.square (SSet.yonedaEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge) ⟨ULift.up 0⟩)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj d.square (SSet.yonedaEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge)
      ⟨ULift.up 1⟩).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq))
    (stableArrowExactMap (d.square.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge)))

/-- 対象座標の移送後も元の指定上辺そのものを保持する。 -/
theorem verdierTopExactMap_original_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    HEq (verdierTopExactMap d)
      (stableArrowExactMap (d.square.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge))) := exactMapTransport_heq _ _ _

/-- 元の上側二胞体の第一短辺は、元の四角形の指定左辺。 -/
theorem verdierUpperTriangle_first_arrow (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 (verdierUpperTriangle d) =
      d.square.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ d.square)) = _
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge]
  rfl

/-- 元の上側二胞体の第二短辺は、元の四角形の指定上辺。 -/
theorem verdierUpperTriangle_last_arrow (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (verdierUpperTriangle d) =
      d.square.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ d.square)) = _
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge]
  rfl

/-- 元の上側合成 path は、指定左辺と指定上辺の同じ実合成。 -/
theorem verdierUpperTriangleCompositeMap_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    HEq (stableTriangleCompositeMap (verdierUpperTriangle d))
      (show d.left ⟶ d.right from (show d.left ⟶ _ from verdierLeftExactMap d) ≫
        (show _ ⟶ d.right from verdierTopExactMap d)) := by
  have hf := (stableArrowExactMap_heq (verdierUpperTriangle_first_arrow d)).trans
    (verdierLeftExactMap_original_heq d).symm
  have hg := (stableArrowExactMap_heq (verdierUpperTriangle_last_arrow d)).trans
    (verdierTopExactMap_original_heq d).symm
  exact (heq_of_eq (stableTriangleCompositeMap_eq_comp _)).trans
    (exactMap_comp_heq
      ((verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq))
      (verdierUpperTriangle_middle d)
      ((verdierUpperTriangle_target d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq)) hf hg)

/-- 元の共有対角座標を指定両端へ戻しても、同じ指定上側合成を回収する。 -/
theorem verdierNullCompositeOriginalMap_upper (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierNullCompositeOriginalMap d 0 =
      (show d.left ⟶ d.right from (show d.left ⟶ _ from verdierLeftExactMap d) ≫
        (show _ ⟶ d.right from verdierTopExactMap d)) := by
  exact eq_of_heq ((exactMapTransport_heq _ _ _).trans
    ((stableTriangleHomOverDiagonal_composite_heq _ _ (verdierTriangle_diagonal d 0)).trans
      (verdierUpperTriangleCompositeMap_heq d)))

/-- 零値関手の元の全 S• 射の合成は、元の完全関手の同じ厳密合成を回収する。 -/
theorem zeroFunctorFullSMap_comp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom))
    (hFG : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F.hom ≫ G.hom))) :
    zeroFunctorFullSMap F hF ≫ coreSExactMap G =
      zeroFunctorFullSMap (show A ⟶ C from (show A ⟶ B from F) ≫ (show B ⟶ C from G)) hFG := by
  apply NatTrans.ext
  funext n
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι).1
  change (zeroFunctorSCoreMap F hF n.unop.len ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sExactMap n.unop.len G).hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι =
    zeroFunctorSCoreMap (show A ⟶ C from (show A ⟶ B from F) ≫ (show B ⟶ C from G)) hFG n.unop.len ≫ _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc, zeroFunctorSCoreMap_ι,
    zeroFunctorSCoreMap_ι]
  exact (sPostcomp_comp n.unop.len F.hom G.hom
    (exactMap_preservesSData F) (exactMap_preservesSData G)).symm

end SerrePositivity.KST.Fibration
