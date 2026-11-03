module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourceRestricted
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourceUniversalData
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningSourceComparisonRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionWitnessComparison

/-!
概要：元の指定始域比較を、F1 の同じ全族比較の指定成分へ値まで同定する。
方針：元の二 prism の一点制限と同じ終点比較の表示を使う。
規約：全係数と指定同型を保持。使われ方：単位三単体の第零面の指定三角形比較。
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
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
  (w : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)

/-- 元の全係数の指定終点比較は、既存の全族比較の同じ一点成分の前合成。 -/
lemma functorHomotopySourceEndpointIso_heq_component :
    HEq (functorHomotopySourceEndpointIso H p s hi w)
      (VertexIso.map
        ((functorHomotopySourceFamilyComparison H p s hi w).app
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
        (relativeFunctorPre (leftUnstraighteningProjection G) p (𝟙 C))) := by
  have hc := unstraighteningSourceComparisonIso_app_pre F G p s hi
    (SSet.const (coherentVertexOfHomotopy H) : (Δ[0] : SSet.{u + 1}) ⟶ _)
    (functorHomotopySourceWrappedMap H p s w)
    (functorHomotopySourceWrappedMap_projection H p s w)
    (functorHomotopySourceWrappedPrism H p s w)
    (functorHomotopySourceWrappedPrism_source H p s w)
    (functorHomotopySourceWrappedPrism_target H p s w)
    (functorHomotopySourceWrappedPrism_projection H p s w)
    (functorHomotopySourceUniversal_projection H p s hi)
    (functorHomotopySourceUniversal_source H s)
    (functorHomotopySourceUniversalMap_projection H p s hi)
    (functorHomotopySourceUniversal_target H s)
    (functorHomotopySourceFamily_initial H p s w)
    (functorHomotopySourceFamily_endpoint H p s w)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) (𝟙 C)
  let w₀ := functorHomotopySourceRestrictedWitness H p s hi w false
  let w₁ := functorHomotopySourceRestrictedWitness H p s hi w true
  have hm := relativeExtensionEndpoint_witnessIso_heq_map pointedSpaceProjection _ _
    (prismEndpoint_zero_leftAnodyne C) _ w₁.initial_base
    (prismEndpoint 1 C) G _ w₁.endpoint_base
    w₀.extension w₁.extension w₀.over w₁.over w₀.initial w₁.initial
    w₀.endpoint w₁.endpoint w₀.endpoint_over w₁.endpoint_over w₀.evaluate w₁.evaluate
  have hr : HEq (functorHomotopySourceRestrictedIso H p s hi w) _ := hm
  exact (functorHomotopySourceEndpointIso_heq_restricted H p s hi w).trans
    (hr.trans hc.symm)

end SerrePositivity.InfinityCategories.F2
