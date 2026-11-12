module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeSectionsMapTransportNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSectionsValueMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceEdgeTransportValue
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FamilyEquivalenceReflection
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
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

attribute [local instance] IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：錐の元の値の切断写像は、同じ錐の辺の値の作用と全族で可換。
方針：pointed fiber の同じ値比較の上で輸送を相殺し、全切断写像の自然性を用いる。
規約：小さい値の持ち上げと切断の縮小同型を保持する。
使われ方：G8 の切断錐から指定極限への値比較。 -/
def coneSectionsValueMap_edgeIso {B : SSet.{u}}
    {F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    {c d : JoinCone F} (e : (sliceOver F).Edge c d) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (spaceInfinityEdgeValue (e.map (sliceOverProjection F))) ≫
          coneSectionsValueMapAt F d d.vertex rfl)
      (coneSectionsValueMapAt F c c.vertex rfl) := by
  letI : KanComplex (simplicialSections (smallLeftUnstraighteningProjection F)) :=
    (coherentSpaceSectionsObject F).isKanComplex
  let P := fun z : SpaceInfinity.{u} _⦋0⦌ => pointedSpaceFiberValueEquivalence z
  let S := smallUnstraighteningSectionsIso F
  let T := edgeTransport pointedSpaceProjection (e.map (sliceOverProjection F))
  have h₁ := FunctorIso.postcomp
    (spaceInfinityEdgeTransportValueIso (e.map (sliceOverProjection F)))
    ((P d.vertex).inv ≫ coneSectionsMap d ≫ S.inv)
  have h₂ := FunctorIso.precomp
    (FunctorIso.postcomp (P d.vertex).homInvIso (coneSectionsMap d ≫ S.inv)) T
  have h₃ := FunctorIso.postcomp (coneSectionsMap_transportIso e).symm S.inv
  have h₄ := (FunctorIso.postcomp (P c.vertex).homInvIso (coneSectionsMap c ≫ S.inv)).symm
  simp only [Category.assoc, Category.id_comp] at h₁ h₂ h₃ h₄
  apply functorIsoOfPrecompEquivalence (P c.vertex).hom (P c.vertex).isQCatEquivalence
  simp only [coneSectionsValueMapAt, QCatEquivalence.symm, Category.assoc]
  exact h₁ ≪≫ h₂ ≪≫ h₃ ≪≫ h₄

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
