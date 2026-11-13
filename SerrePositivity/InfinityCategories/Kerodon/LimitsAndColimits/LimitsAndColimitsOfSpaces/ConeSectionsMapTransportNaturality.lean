module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeSectionsHomActionEdgeComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeSectionsHomActionVertexComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalPostcomposeIdentityFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Identity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.PointedIntervalTransportVertexComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.FixedApexConeEdgeComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSectionsNativeComparison

/-!
概要：元の錐の全切断への全 Hom 作用は、指定された錐の辺の標準後合成と可換。
方針：元の native Hom 比較の辺の同型を、同じ全切断作用の比較で移す。
規約：全 Hom をパラメータにし、試験空間の点へ弱めない。
使われ方：G8 の切断錐から指定極限への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces Equivalence
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

attribute [local instance] IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：元の錐の切断写像は、同じ錐の辺の頂点輸送と全 fiber 上で可換。
方針：全 Hom 作用の辺の比較を恒等辺で評価し、同じ区間模型の単位則で元の辺を回収する。
規約：fiber の各頂点だけでなく写像全体の同型。
使われ方：G8 の切断錐から指定極限錐への比較。 -/
def coneSectionsMap_transportIso {B : SSet.{u + 1}}
    {F : B ⟶ SpaceInfinity.{u}} {c d : JoinCone F}
    (e : (sliceOver F).Edge c d) :
    FunctorIso (coneSectionsMap c)
      (edgeTransport pointedSpaceProjection (e.map (sliceOverProjection F)) ≫ coneSectionsMap d) := by
  letI : KanComplex (simplicialSections
      (SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F)) :=
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex _
  let z := c.vertex
  let a := e.map (sliceOverProjection F)
  let s := (pinchedHomVertexEquiv z z).symm (SSet.Edge.id z)
  let post := postcompose z (SSet.Truncated.HomotopyCategory.homMk a)
  have hs : (pinchedHomToIntervalMappingSpace z z).app _ s =
      intervalMappingVertexOfEdge (SSet.Edge.id z) := by
    rw [pinchedHomToIntervalMappingSpace_vertex]
    exact congrArg intervalMappingVertexOfEdge ((pinchedHomVertexEquiv z z).apply_symm_apply _)
  have h₀ := coneSectionsHomAction_intervalVertexIso c z s (SSet.Edge.id z) (eqToIso (congrArg HomotopyCategory.mk hs))
  have hunit := FunctorIso.postcomp (edgeTransport_identity_iso pointedSpaceProjection z).some
    (coneSectionsMap c)
  simp only [Category.id_comp] at hunit
  have hleft := h₀ ≪≫ hunit
  have hleft' : VertexIso ((coneSectionsHomAction c z).app _ s)
      (functorVertex (coneSectionsMap c)) := by
    change VertexIso (functorVertex _) (functorVertex _) at hleft
    have hv : functorVertex ((functorVertexEquiv _ _).symm
        ((coneSectionsHomAction c z).app _ s)) = (coneSectionsHomAction c z).app _ s :=
      (functorVertexEquiv _ _).apply_symm_apply _
    rw [hv] at hleft
    exact hleft
  have hcomp := (liftMapComparisonIso
    (intervalPostcompose z (SSet.Truncated.HomotopyCategory.homMk a))).app s
  change VertexIso ((pinchedHomToIntervalMappingSpace z d.vertex).app _ (post.app _ s))
    ((intervalPostcompose z (SSet.Truncated.HomotopyCategory.homMk a)).app _
      ((pinchedHomToIntervalMappingSpace z z).app _ s)) at hcomp
  rw [hs] at hcomp
  let v : (Δ[0] : SSet.{u + 1}) _⦋0⦌ := SSet.yonedaEquiv (𝟙 Δ[0])
  have hconst := (functorIsoOfSimplicialHomotopy
    (intervalPostcompose_identityFamily_homotopy (A := (Δ[0] : SSet.{u + 1})) a).some).app v
  change VertexIso
    ((intervalPostcompose z (SSet.Truncated.HomotopyCategory.homMk a)).app _
      (intervalMappingVertexOfEdge (SSet.Edge.id z))) (intervalMappingVertexOfEdge a) at hconst
  have h₁ := coneSectionsHomAction_intervalVertexIso d z (post.app _ s) a (hcomp ≪≫ hconst)
  have hright : VertexIso ((coneSectionsHomAction d z).app _ (post.app _ s))
      (functorVertex (edgeTransport pointedSpaceProjection a ≫ coneSectionsMap d)) := by
    change VertexIso (functorVertex _) (functorVertex _) at h₁
    have hv : functorVertex ((functorVertexEquiv _ _).symm
        ((coneSectionsHomAction d z).app _ (post.app _ s))) =
        (coneSectionsHomAction d z).app _ (post.app _ s) :=
      (functorVertexEquiv _ _).apply_symm_apply _
    rw [hv] at h₁
    exact h₁
  exact hleft'.symm ≪≫ (coneSectionsHomAction_edgeIso e z).app s ≪≫ hright

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
