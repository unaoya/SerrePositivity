module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeKanObjects
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.EdgeApexPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：元の native 比較の coherent な辺を、元の余極限頂点からの可逆頂点円柱にする。
方針：同じ比較辺の全一単体を保持し、証明済みのホモトピー逆から可逆性を得る。
規約：元の頂点と比較辺を保持。使われ方：a7 の余極限後の native 極限錐の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)

/-- 元の native 比較の全一単体による頂点円柱。 -/
def coherentCospanNativeComparisonApexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  edgeApexPrism (coherentNerveEdge (coherentCospanNativeComparisonKanMap F X Y Z C))

/-- 円柱の始点は元の coherent 図式の余極限頂点そのもの。 -/
lemma coherentCospanNativeComparisonApexPrism_zero :
    prismEndpoint 0 (Δ[0] : SSet.{u + 1}) ≫
      coherentCospanNativeComparisonApexPrism F X Y Z C =
        SSet.yonedaEquiv.symm (coherentDiagramTotalVertex F) := by
  exact (edgeApexPrism_zero _).trans
    (congrArg SSet.yonedaEquiv.symm (coherentNerveVertex_object (coherentDiagramTotalVertex F)))

/-- 円柱の終点は元の native 二射の区間引き戻しの頂点。 -/
lemma coherentCospanNativeComparisonApexPrism_one :
    prismEndpoint 1 (Δ[0] : SSet.{u + 1}) ≫
      coherentCospanNativeComparisonApexPrism F X Y Z C =
        SSet.yonedaEquiv.symm (coherentNerveVertex (intervalPullbackKanObject
          (coherentCospanNativeLeftKanMap F X Y Z C)
          (coherentCospanNativeRightKanMap F X Y Z C))) := edgeApexPrism_one _

/-- 各点の極限性から、同じ比較の頂点円柱の全垂直辺が可逆。 -/
lemma coherentCospanNativeComparisonApexPrism_vertical_isInvertible [IsFilteredInfinity B]
    (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b))
    (x : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex ((coherentCospanNativeComparisonApexPrism F X Y Z C).app
      (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})),
        PinchedHom.constant x 1))) := by
  exact edgeApexPrism_vertical_isInvertible _
    (coherentKanEdge_isInvertible_of_isQCatEquivalence
      (coherentCospanConeNativeComparison_homotopyEquivalence F X Y Z C hc).isQCatEquivalence) x

end SerrePositivity.InfinityCategories.F2
