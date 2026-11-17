module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldCoherentComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：同じ指定coherent比較を、元のscaffold上の同じ二脚へ制限する。
方針：選択条件に保持した相対同型を忘却し、指定embeddingで前合成する。
規約：Kerodon Corollary 5.6.0.6（Tag 028T）、HTT §3.3.2の既存構成の制限法則。
使われ方：S8で、元の指定復元比較を全係数のscaffoldの比較へ接続する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定比較は、元のuniversal scaffoldとtaut scaffoldの同じ比較に沿って制限される。 -/
def scaffoldCoherentComparison_scaffoldIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (universalScaffold p) ≫
        scaffoldCoherentComparison p)
      ((SSet.uliftFunctor.{u + 1, u}).map (tautScaffold (leftStrictTransportDiagram p)) ≫
        leftCoherentTransportComparison p) := by
  let s := scaffoldTransportComparisonSpan p
  let U := SSet.uliftFunctor.{u + 1, u}
  let q := leftUnstraighteningProjection (leftCoherentTransport p)
  have e : FunctorIso
      (s.toStrictTransportComparisonSpan.coherentSource ≫ scaffoldCoherentComparison p)
      s.toStrictTransportComparisonSpan.coherentTarget :=
    (scaffoldCoherentComparison_restrictionIso p).map
      (vertexFiberι ((ihom (U.obj s.total)).map q)
        (functorVertex s.toStrictTransportComparisonSpan.coherentBase))
  let e' := e.precomp (U.map s.embedding)
  have hL : U.map s.embedding ≫
      (s.toStrictTransportComparisonSpan.coherentSource ≫ scaffoldCoherentComparison p) =
      U.map (universalScaffold p) ≫ scaffoldCoherentComparison p := by
    change U.map s.embedding ≫ (U.map s.source ≫ scaffoldCoherentComparison p) = _
    rw [← Category.assoc, ← U.map_comp, s.source_restriction]
  have hR : U.map s.embedding ≫ s.toStrictTransportComparisonSpan.coherentTarget =
      U.map (tautScaffold (leftStrictTransportDiagram p)) ≫ leftCoherentTransportComparison p := by
    change U.map s.embedding ≫ (U.map s.weighted ≫ leftCoherentTransportComparison p) = _
    rw [← Category.assoc, ← U.map_comp, s.weighted_restriction]
  exact (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hL)).symm ≪≫
    e' ≪≫ eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hR)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
