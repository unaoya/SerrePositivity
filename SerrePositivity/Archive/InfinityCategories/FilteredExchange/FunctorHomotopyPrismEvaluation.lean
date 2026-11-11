module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismSection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeRestrictedEndpointUncurry
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorPostUncurry

/-!
概要：元の普遍 prism の全始点評価は恒等射、全終点評価は元の選択済み作用。
方針：全パラメータの実延長を端点で評価し、引き戻しの二射影で比較する。
規約：始域射を固定しない。使われ方：始点も動く prism 比較の指定自然性。
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
local notation "U" => relativeFunctorSpace (leftUnstraighteningProjection F) p

/-- 全相対 prism を、同じ元の始域図式の全空間への実始域射へ評価する。 -/
def functorHomotopyPrismSourceEvaluation : relativeFunctorSpace pointedSpaceProjection d ⟶ U :=
  relativeFunctorRestrictedEndpoint pointedSpaceProjection d (prismEndpoint 0 C) F p
    (functorHomotopyPrismBase_source H p)

/-- 全相対 prism を、同じ元の標的図式の全空間への実終点射へ評価する。 -/
def functorHomotopyPrismTargetEvaluation : relativeFunctorSpace pointedSpaceProjection d ⟶
    relativeFunctorSpace (leftUnstraighteningProjection G) p :=
  relativeFunctorRestrictedEndpoint pointedSpaceProjection d (prismEndpoint 1 C) G p
    (functorHomotopyPrismBase_target H p)

/-- 元の普遍 prism の全始点評価は、元の全始域射を厳密に回収する。 -/
lemma functorHomotopyPrismSection_source :
    functorHomotopyPrismSection H p ≫ functorHomotopyPrismSourceEvaluation H p = 𝟙 U := by
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [functorHomotopyPrismSourceEvaluation, relativeFunctorRestrictedEndpoint_uncurry,
      functorHomotopyPrismSection_uncurry, functorHomotopyPrismSectionLift_source]
  · exact (relativeFunctorUncurry_projection _).trans (relativeFunctorUncurry_projection _).symm

/-- 元の普遍 prism の全終点評価は、同じ選択済み作用による相対後合成。 -/
lemma functorHomotopyPrismSection_target :
    functorHomotopyPrismSection H p ≫ functorHomotopyPrismTargetEvaluation H p =
      HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
        (leftUnstraighteningProjection G)
        (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
        (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p := by
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [functorHomotopyPrismTargetEvaluation, relativeFunctorRestrictedEndpoint_uncurry,
      functorHomotopyPrismSection_uncurry, functorHomotopyPrismSectionLift_target]
    have ht := relativeFunctorPost_uncurry (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G)
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p (𝟙 U)
    simpa only [Category.id_comp, Category.assoc] using
      (congrArg (fun z => z ≫ pullback.fst pointedSpaceProjection G) ht).symm
  · exact (relativeFunctorUncurry_projection _).trans (relativeFunctorUncurry_projection _).symm

end SerrePositivity.InfinityCategories.F2
