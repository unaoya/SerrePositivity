module
public import SerrePositivity.KST.Fibration.VerdierFullSLowerMaximalFaces
public import SerrePositivity.KST.Fibration.CoherentTriangleShortFaces

/-!
概要：指定 Verdier 下側の最大 path 図式の、元の短辺を持つ通常の射列を回収する。
方針：F1 の実 strict 図式の Hom 頂点公式を、同じ下側二胞体と元の短 path へ適用する。
規約：元の全二胞体からの全関手同型を保持する。共有対角の上側との整合は別工程。
使われ方：K-6 c4 の指定包含・商を持つ標準合成二胞体との全比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SimplicialThickening SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 元の同じ下側二胞体の最大 path による実通常図式。 -/
def verdierFullSLowerStrictDiagram : ULift.{u} (Fin 3) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexStrictDiagram (verdierFullSLowerSimplex d)

/-- 同じ実通常図式の第一射の Hom 頂点は、元の全第一短辺の同じ Hom 頂点。 -/
theorem verdierFullSLowerStrictDiagram_first_vertex :
    SimplicialCategory.homEquiv' _ _ ((verdierFullSLowerStrictDiagram d).map
      (homOfLE (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide))) =
    coherentArrowHomVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 2 (verdierFullSLowerSimplex d)) := by
  change SimplicialCategory.homEquiv' _ _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (verdierFullSLowerSimplex d)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1
        from by decide))) = _
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex (verdierFullSLowerSimplex d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1
      from by decide))).trans ?_
  change coherentTriangleHomVertex (verdierFullSLowerSimplex d) _ = _
  exact (congrArg (coherentTriangleHomVertex (verdierFullSLowerSimplex d))
    (coherentTriangleFirstPath_unique _)).trans (coherentTriangleFirst_vertex _)

/-- 同じ実通常図式の第二射の Hom 頂点は、元の全第二短辺の同じ Hom 頂点。 -/
theorem verdierFullSLowerStrictDiagram_last_vertex :
    SimplicialCategory.homEquiv' _ _ ((verdierFullSLowerStrictDiagram d).map
      (homOfLE (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide))) =
    coherentArrowHomVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 0 (verdierFullSLowerSimplex d)) := by
  change SimplicialCategory.homEquiv' _ _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (verdierFullSLowerSimplex d)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2
        from by decide))) = _
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex (verdierFullSLowerSimplex d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2
      from by decide))).trans ?_
  change coherentTriangleHomVertex (verdierFullSLowerSimplex d) _ = _
  exact (congrArg (coherentTriangleHomVertex (verdierFullSLowerSimplex d))
    (coherentTriangleLastPath_unique _)).trans (coherentTriangleLast_vertex _)

end SerrePositivity.KST.Fibration
