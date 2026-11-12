module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingLargeInvariance
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：大宇宙の実 cell 写像関手を全単体の空間値図式とし、元の擬同型辺を反転する。
方針：既存の Kan 図式の coherent 表示と一単体の実計算を使う。
規約：指定の代数局所化への因子化や導来比較は結論に含めない。
使われ方：元の dg 代数表示と実写像模型との全単体の比較の入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

def multiplicativeCellMappingInfinityCoherent :
    SSet.uliftFunctor.{u + 2, u + 1}.obj (nerve (InfinityPresentation R)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (multiplicativeCellMappingInfinityKanFunctor R A)

set_option maxHeartbeats 800000 in -- 元の提示の射と大宇宙の実 Kan 写像の表示を照合する。
lemma multiplicativeCellMappingInfinityCoherent_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (multiplicativeCellMappingInfinityCoherent R A)
      (ULift.up.{u + 2, u + 1} '' quasiIsoInfinityEdges R) := by
  rintro _ ⟨s, hs, rfl⟩
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
    (multiplicativeCellMappingInfinity_target_isQCatEquivalence R A s.hom hs)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ULift.up.{u + 2, u + 1} s)).map
      ((truncation 2).map (multiplicativeCellMappingInfinityCoherent R A)))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      ((multiplicativeCellMappingInfinityKanFunctor R A).map s.hom)).toTruncated) ?_).mpr hi
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (multiplicativeCellMappingInfinityKanFunctor R A)).app
    (Opposite.op ⦋1⦌) (ULift.up s) = _
  have hs' : (nerve.edgeMk s.hom).edge = s := ComposableArrows.ext₁ rfl rfl rfl
  simpa only [hs', SSet.Edge.toTruncated_edge] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_edge (multiplicativeCellMappingInfinityKanFunctor R A) s.hom)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
