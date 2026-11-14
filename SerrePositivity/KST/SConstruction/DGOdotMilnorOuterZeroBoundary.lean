module
public import SerrePositivity.KST.SConstruction.DGKFixedNullPerfectZeroIso
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuSourceSquare
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualRectangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：LT 外周の絶対提示と実固定 ν 零化面の零角を、同じ全対象商を保って比較する。
方針：標準零 Cat^perf と元全対象商の指定同型を、元の両零角頂点へ照合する。
規約：零角の実全比較であり、外周全体の VerdierSquareDiagramIso とは区別する。
使われ方：LT 外周の指定三境界のうち、供給に依存しない零角境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "A" => dgOdotMilnorSourceCellInput R d
local notation "Z" => dgKInputStableValue R (dgFixedNullInput R (A))
local notation "hZ" => dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R (A))

/-- 概要：絶対LT 外周と元実 ν 面の零角は指定 Cat^perf 頂点同型を持つ。
方針：同じ全対象商の零頂点同型を、元両四角形の零角へ厳密に照合する。
規約：元全対象商の頂点を保持。使われ方：外周の零角全比較の成分。 -/
def dgOdotMilnorOuterZeroVertexIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorActualOuterDiagram R d h).square 0 1)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R) 0 1) := by
  have hs : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorActualOuterDiagram R d h).square 0 1 =
      perfectStableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} perfectZeroCategory_isIdempotentComplete := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((dgOdotMilnorCompletedLaxQuotient R d h).outerSquare ≫
      perfectStableInfinityInclusion) 0 1 = _
    rw [PerfectLaxQuotient.outerSquare_inclusion]
    exact (dgOdotMilnorCompletedLaxQuotient R d h).rawOuterSquare_vertices.2.2.2
  have ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R) 0 1 =
      perfectStableVertex (Z) (hZ) := by
    change (dgKInputPerfectNu R).app _
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorSourceNullOuterSquare R d) 0 1) = _
    rw [dgOdotMilnorSourceNullOuterSquare_zero_vertex, dgKInputPerfectNu_vertex]
  exact eqToIso (congrArg HomotopyCategory.mk hs) ≪≫
    dgKFixedNullPerfectZeroIso R (A) ≪≫ (eqToIso (congrArg HomotopyCategory.mk ht)).symm

/-- 概要：同じ零角の指定同型は零単体全体の関手同型を与える。
方針：零単体上の関手評価の充満忠実性で指定頂点同型を戻す。
規約：零角の同型類だけでは代用しない。使われ方：Sp 正本の指定零角境界。 -/
def dgOdotMilnorOuterZeroBoundary : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierZeroCorner ≫ (dgOdotMilnorActualOuterDiagram R d h).square)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierZeroCorner ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pointFunctorEvaluationIso
    perfectStableInfinity.{u + 1})).isQCatEquivalence.isFullyFaithful.preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorActualOuterDiagram R d h).square 0 1)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R) 0 1)
  exact dgOdotMilnorOuterZeroVertexIso R d h
end SerrePositivity.KST.SConstruction
