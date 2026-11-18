module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningLimitTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitVertex

/-!
概要：全分類図式の指定同型で、同じ底係数を持つ二つの指定極限の頂点を比較する。
方針：既存の復元比較と小さい unstraightening の比較で、極限の一意性を合成する。
規約：元の極限錐を引数に保ち、分類図式の同型を対象ごとの仮定に置き換えない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、HTT 5.1.5.6、S8。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {E F B X : SSet.{u}} [Quasicategory B] [Quasicategory X]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]

/-- 同じ分類図式の指定同型で、同じ底係数の指定極限の頂点を比較する。
Kerodon Corollary 5.6.0.6（Tag 028T）、既存の復元比較・制限・極限の一意性の合成則。 -/
def limitVertexIsoOfLeftStraighteningIso
    (e : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))
    (O : B ⟶ X) (c : JoinCone (p ≫ O)) (d : JoinCone (q ≫ O))
    (hc : IsLimitCone c) (hd : IsLimitCone d) : VertexIso c.vertex d.vertex := by
  letI : Quasicategory E := quasicategory_of_innerFibration p
  letI : Quasicategory F := quasicategory_of_innerFibration q
  have hp : HasLimit
      (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O) := by
    apply (hasLimit_iff_equivalentRestriction (leftStraighteningInfinityReconstruction p)
      (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence _).mpr
    simpa only [← Category.assoc, leftStraighteningInfinityReconstruction_projection] using
      (show HasLimit (p ≫ O) from ⟨c, hc⟩)
  have hq : HasLimit
      (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O) := by
    apply (hasLimit_iff_equivalentRestriction (leftStraighteningInfinityReconstruction q)
      (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q).isQCatEquivalence _).mpr
    simpa only [← Category.assoc, leftStraighteningInfinityReconstruction_projection] using
      (show HasLimit (q ≫ O) from ⟨d, hd⟩)
  let s := Classical.choose hp
  let t := Classical.choose hq
  have hs := Classical.choose_spec hp
  have ht := Classical.choose_spec hq
  let ep := limitVertexIsoOfOverEquivalence (leftStraighteningInfinityReconstruction p)
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence
    (leftStraighteningInfinityReconstruction_projection p) O c s hc hs
  let eq := limitVertexIsoOfOverEquivalence (leftStraighteningInfinityReconstruction q)
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q).isQCatEquivalence
    (leftStraighteningInfinityReconstruction_projection q) O d t hd ht
  let em := limitVertexIsoOfOverEquivalence (smallLeftUnstraighteningComparisonOfFunctorIso e)
    (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence e).isQCatEquivalence
    (smallLeftUnstraighteningComparisonOfFunctorIso_projection e) O s t hs ht
  exact ep ≪≫ em ≪≫ eq.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
