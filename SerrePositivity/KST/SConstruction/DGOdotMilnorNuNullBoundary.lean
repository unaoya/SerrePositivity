module
public import SerrePositivity.KST.SConstruction.DGKFixedNullPerfectZeroIso
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuProjectionArrow
public import SerrePositivity.KST.SConstruction.PerfectStableHoArrow
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.KST.LocalizingInvariants.RelativeVerdierDiagramComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：同じ実核零化面の包含・商・零角の指定比較を具体的に束ねる。
方針：元の商辺比較と全対象商の実零性から、Cat^perf 内の零角の同型を作る。
規約：境界比較を全四角形比較の存在と取り違えない。
使われ方：Sp 正本の VerdierSquareDiagramIso の相対延長に指定する三境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Z" => dgKInputStableValue R
  (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))
local notation "hZ" => dgKInputStableValue_isIdempotentComplete R
  (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))

/-- 概要：標準零安定圏と同じ全対象商の Perf 値の指定 Cat^perf 同型。
方針：元の零圏を往復する実完全射と全零図式の同型を使う。
規約：元の全対象商の頂点を保つ。使われ方：実零角の指定比較。 -/
def dgOdotMilnorNuNullZeroVertexIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (perfectStableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1}
      perfectZeroCategory_isIdempotentComplete) (perfectStableVertex (Z) (hZ)) :=
  dgKFixedNullPerfectZeroIso R (dgOdotMilnorFlatKernelInput R d)

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：絶対核列の零角と実 ν 面の零角を同じ指定頂点同型で比較する。
方針：元の全単体を保つ提示と同じ実零角の頂点式で照合する。
規約：別の零角を選び直さない。使われ方：零角の全図式比較への入力。 -/
def dgOdotMilnorNuNullSquareZeroVertexIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorNuPerfectSequence R d h).presentation.square 0 1)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) 0 1) := by
  have hs : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorNuPerfectSequence R d h).presentation.square 0 1 =
      perfectStableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} perfectZeroCategory_isIdempotentComplete := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierSquare _ ≫ perfectStableInfinityInclusion) 0 1 = _
    rw [perfectVerdierSquare_inclusion]
    exact (perfectVerdierRawSquare_vertices (dgOdotMilnorNuPerfectSequence R d h)).2.2.2
  have ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) 0 1 =
      perfectStableVertex (Z) (hZ) := by
    change (dgKInputPerfectNu R).app _
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorPerfectNullSquare R d) 0 1) = _
    rw [dgOdotMilnorPerfectNullSquare_zero_vertex, dgKInputPerfectNu_vertex]
  exact eqToIso (congrArg HomotopyCategory.mk hs) ≪≫
    dgOdotMilnorNuNullZeroVertexIso R d ≪≫ (eqToIso (congrArg HomotopyCategory.mk ht)).symm

/-- 概要：同じ二つの零角は Δ[0] 上の関手として指定同型で結ばれる。
方針：指定頂点同型を定値図式関手で写し、同じ Yoneda 射へ戻す。
規約：端点の同型類だけで代用しない。使われ方：Sp の零角境界。 -/
def dgOdotMilnorNuNullSquareZeroBoundary : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierZeroCorner ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierZeroCorner ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pointFunctorEvaluationIso
    perfectStableInfinity.{u + 1})).isQCatEquivalence.isFullyFaithful.preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorNuPerfectSequence R d h).presentation.square 0 1)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) 0 1)
  exact dgOdotMilnorNuNullSquareZeroVertexIso R d h

/-- 概要：同じ実 ν 核面に対する包含・商・零角の指定三境界。
方針：構成した同じ三つの全比較を束ねる。
規約：全四角形同型の相対延長は未完。使われ方：Sp 正本の全比較型の境界引数。 -/
def dgOdotMilnorNuNullSquareBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso
    (dgOdotMilnorNuPerfectSequence R d h).presentation.square
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) where
  inclusion := dgOdotMilnorNuNullSquareInclusionBoundary R d h
  quotient := dgOdotMilnorNuNullSquareProjectionBoundary R d h
  zero := dgOdotMilnorNuNullSquareZeroBoundary R d h

end SerrePositivity.KST.SConstruction
