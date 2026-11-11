module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeRestrictedEndpointFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialKanFunctorIsoProjection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIso

/-!
概要：始点も動く全 prism の普遍持ち上げと元の実 prism を、始点上で比較する。
方針：始点評価の厳密な切断と全境界持ち上げから、同じ fiber 内の全関手同型を取る。
規約：元の切断と実終点を保持。使われ方：共有辺の指定比較の全自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B)
local notation "d" => (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)
local notation "L" => relativeFunctorSpace pointedSpaceProjection d
local notation "q" => functorHomotopyPrismSourceEvaluation H p
local notation "r" => functorHomotopyPrismTargetEvaluation H p
local notation "s" => functorHomotopyPrismSection H p

/-- 同じ元の全 prism の始点評価は、全境界を持ち上げる。 -/
lemma functorHomotopyPrismSourceEvaluation_trivialKanFibration : TrivialKanFibration q :=
  relativeFunctorRestrictedEndpoint_trivialKanFibration pointedSpaceProjection d
    (prismEndpoint 0 C) F p (functorHomotopyPrismBase_source H p)
    (prismEndpoint_zero_leftAnodyne C)

/-- 普遍切断と元の実 prism は、元の同じ始点射の上にある。 -/
lemma functorHomotopyPrismSectionComparison_over :
    (q ≫ s) ≫ q = (𝟙 L) ≫ q := by
  rw [Category.assoc, functorHomotopyPrismSection_source, Category.comp_id, Category.id_comp]

/-- 元の全始点射を固定したまま、普遍 prism と実 prism の全族を比較する。 -/
def functorHomotopyPrismSectionComparison : FunctorIso (q ≫ s) (𝟙 L) := by
  have := functorHomotopyPrismSourceEvaluation_trivialKanFibration H p
  exact functorIsoOfTrivialKanFibration q (q ≫ s) (𝟙 L)
    (functorHomotopyPrismSectionComparison_over H p)

/-- 同じ全族比較は、始点評価で元の厳密な一致の同型へ戻る。 -/
lemma functorHomotopyPrismSectionComparison_source :
    (functorHomotopyPrismSectionComparison H p).postcomp q =
      eqToIso (congrArg (fun v => SSet.HomotopyCategory.mk (functorVertex v))
        (functorHomotopyPrismSectionComparison_over H p)) := by
  have := functorHomotopyPrismSourceEvaluation_trivialKanFibration H p
  exact functorIsoOfTrivialKanFibration_postcomp q _ _
    (functorHomotopyPrismSectionComparison_over H p)

/-- 始点も動く全 prism の元の実終点と、同じ native 作用の全自然な比較。 -/
def functorHomotopyPrismEndpointComparison :
    FunctorIso (q ≫ HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G)
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p) r := by
  have hs : (q ≫ s) ≫ r = q ≫ HomotopyLimits.relativeFunctorPost
      (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p := by
    rw [Category.assoc, functorHomotopyPrismSection_target]
  exact (functorEqIso hs).symm ≪≫
    (functorHomotopyPrismSectionComparison H p).postcomp r ≪≫ functorEqIso (Category.id_comp r)

end SerrePositivity.InfinityCategories.F2
