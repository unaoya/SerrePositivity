module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyDiagram

/-!
概要：coherent ホモロジー図式の射は、元の辺の鎖写像が誘導する射である。
方針：辺の代表元上で H⁰ 比較を評価し、ホモトピー商のホモロジー比較を使う。
規約：合成の HA データは保持し、辺の鎖写像を strict 図式へ貼り合わせない。
使われ方：単体次元フィルトレーションの次数一微分の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarDiagramEdge {j k : J} (f : j ⟶ k) :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G (nerveEquiv.symm j)) ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G (nerveEquiv.symm k)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up.{u, max (u + 1) v} (X := nerve J)
      (CategoryTheory.nerve.edgeMk f).toTruncated).map ((SSet.truncation 2).map G))

lemma dgCoherentBarHomotopyDiagram_map {j k : J} (f : j ⟶ k) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomotopyDiagram R D G).map f =
      (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map (dgCoherentBarDiagramEdge R D G f) := rfl

lemma dgCoherentBarHomologyDiagramObjIso_naturality (x : D) (q : ℤ)
    {j k : J} (f : j ⟶ k) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x q).map f ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D G x q k).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D G x q j).hom ≫
      HomologicalComplex.homologyMap
        ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgCoherentBarDiagramEdge R D G f)) q :=
  (_root_.HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) q).hom.naturality
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgCoherentBarDiagramEdge R D G f))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
