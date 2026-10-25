module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyDiagram

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

def dgCoherentBarDiagramEdge {j k : J} (f : j ⟶ k) :
    ForgetEnrichment.of (Complex R) (coherentDiagramVertex G (nerveEquiv.symm j)) ⟶
      ForgetEnrichment.of (Complex R) (coherentDiagramVertex G (nerveEquiv.symm k)) :=
  DGNerve.HomotopyComparison.edgeClosed
    ((UniverseEdge.up.{u, max (u + 1) v} (X := nerve J)
      (CategoryTheory.nerve.edgeMk f).toTruncated).map ((SSet.truncation 2).map G))

lemma dgCoherentBarHomotopyDiagram_map {j k : J} (f : j ⟶ k) :
    (dgCoherentBarHomotopyDiagram R D G).map f =
      (moduleToHomotopy R D).map (dgCoherentBarDiagramEdge R D G f) := rfl

lemma dgCoherentBarHomologyDiagramObjIso_naturality (x : D) (q : ℤ)
    {j k : J} (f : j ⟶ k) :
    (dgCoherentBarHomologyDiagram R D G x q).map f ≫
      (dgCoherentBarHomologyDiagramObjIso R D G x q k).hom =
    (dgCoherentBarHomologyDiagramObjIso R D G x q j).hom ≫
      HomologicalComplex.homologyMap
        ((moduleEvaluation R D x).map (dgCoherentBarDiagramEdge R D G f)) q :=
  (_root_.HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) q).hom.naturality
    ((moduleEvaluation R D x).map (dgCoherentBarDiagramEdge R D G f))

end SerrePositivity.InfinityCategories
