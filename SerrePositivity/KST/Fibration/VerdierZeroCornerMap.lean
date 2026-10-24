module
public import SerrePositivity.KST.Fibration.ZeroTargetCornerEquivalence
public import SerrePositivity.KST.Fibration.ExactMapCoordinates
public import SerrePositivity.KST.Fibration.StableHomVertexRecovery
public import SerrePositivity.InfinityCategories.F1.Coherent.MapSmallness
public import SerrePositivity.KST.Fibration.ExInfinityCommSqEdges
public import SerrePositivity.KST.Fibration.KanTerminalComparison

/-!
概要：指定 Verdier 四角形の実左辺を用いた、元の相対 S 核の零角比較。
方針：coherent 左辺から完全射を回収し、元の対象等号に沿ってのみ輸送する。
規約：任意の零値関手や終対象間同型を選び直さない。
使われ方：商核四角形と指定 Verdier 四角形の全比較の左面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 指定した同じ coherent 左辺から回収した、同じ零角への完全関手。 -/
def verdierLeftExactMap (d : VerdierDiagram.{u}) :
    ExactMap d.left (stableObject (squareVertex d.square 0 1)) :=
  exactMapTransport
    ((coherentMap_simplex_obj d.square (SSet.yonedaEquiv squareLeftEdge)
      ⟨ULift.up 0⟩).trans (congrArg stableObject d.left_eq))
    (coherentMap_simplex_obj d.square (SSet.yonedaEquiv squareLeftEdge) ⟨ULift.up 1⟩)
    (stableArrowExactMap (d.square.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv squareLeftEdge)))

/-- 対象座標の移送後も、元の左辺から回収した同じ完全射を保持する。 -/
theorem verdierLeftExactMap_original_heq (d : VerdierDiagram.{u}) :
    HEq (verdierLeftExactMap d)
      (stableArrowExactMap (d.square.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv squareLeftEdge))) :=
  exactMapTransport_heq _ _ _

/-- 指定左辺を、元の商核の全相対 S 図式に作用させた零角比較。 -/
def verdierRelativeSZeroCornerMap (d : VerdierDiagram.{u}) :
    relativeSimplicialSConstruction (d.inclusion.hom ≫ d.projection.hom) ⟶
      simplicialSConstruction (stableObject (squareVertex d.square 0 1)).obj ⋙
        quasicategoryCoreFunctor :=
  relativeSZeroTargetCornerMap _ (verdierLeftExactMap d) d.zero_corner

/-- 元の核包含後の比較は、指定 Verdier 左辺の core S• 作用に厳密一致する。 -/
theorem verdierRelativeSZeroCornerMap_left (d : VerdierDiagram.{u}) :
    relativeSimplicialSConstructionCoreInclusion (d.inclusion.hom ≫ d.projection.hom) ≫
        verdierRelativeSZeroCornerMap d = coreSExactMap (verdierLeftExactMap d) :=
  relativeSZeroTargetCornerMap_left _ _ _

/-- この指定左辺から作った実角比較は、同じ局所化で可逆。 -/
theorem verdierRelativeSZeroCornerMap_localized_isIso (d : VerdierDiagram.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (verdierRelativeSZeroCornerMap d))) :=
  relativeSZeroTargetCornerMap_localized_isIso d.isVerdier _ d.zero_corner

/-- 元の零角比較の Ex∞ 像を、同じ実 Kan 複体間の射として保持する。 -/
def verdierRelativeSZeroCornerKanMap (d : VerdierDiagram.{u}) :=
  exInfinityKanMap (simplicialDiagonalFunctor.map (verdierRelativeSZeroCornerMap d))

/-- 同じ元の零角比較の coherent 辺そのものが可逆。 -/
theorem verdierRelativeSZeroCornerKanMap_isInvertible (d : VerdierDiagram.{u}) :
    IsInvertibleEdge (coherentNerveEdge (verdierRelativeSZeroCornerKanMap d)) := by
  apply coherentKanEdge_isInvertible_of_isQCatEquivalence
  apply isQCatEquivalence_of_anodyneQ_isIso
  exact (exInfinity_map_localized_isIso_iff _).mpr
    (verdierRelativeSZeroCornerMap_localized_isIso d)

/-- Kan 化後も、元の核包含と指定 Verdier 左辺との厳密可換性を保持する。 -/
theorem verdierRelativeSZeroCornerKanMap_left (d : VerdierDiagram.{u}) :
    exInfinityKanMap (simplicialDiagonalFunctor.map
        (relativeSimplicialSConstructionCoreInclusion
          (d.inclusion.hom ≫ d.projection.hom))) ≫
        verdierRelativeSZeroCornerKanMap d =
      exInfinityKanMap (simplicialDiagonalFunctor.map (coreSExactMap (verdierLeftExactMap d))) := by
  change exInfinity.map _ ≫ exInfinity.map _ = exInfinity.map _
  rw [← Functor.map_comp, ← Functor.map_comp, verdierRelativeSZeroCornerMap_left]

end SerrePositivity.KST.Fibration
