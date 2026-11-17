module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyComponent
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-!
概要：通常の自然変換を準圏に送った同じ全ホモトピーを、成分の可逆性から反転する。
方針：元のnerve円柱の各頂点の辺を照合し、既存の全関手圏の辺の判定を使う。
規約：IS-W2 R03dの既存の反転・自然性の法則。対象ごとの同型を選び直さない。
使われ方：全始域・全次数のaugmentationを一つの全関手同型として反転する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open CategoryTheory SSet
open SerrePositivity.SimplicialModel
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  {F G : I ⥤ C} (η : F ⟶ G) {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)

/-- 元の自然変換のnerve円柱を、同じ標的関手で送った全ホモトピー。 -/
def nerveTransformationPostHomotopy : SSet.Homotopy (nerveMap F ≫ L) (nerveMap G ≫ L) :=
  HomotopyClasses.postHomotopy L (nerveNatTransHomotopy η)

/-- 元の成分の辺を同じ関手が反転するなら、その全自然変換自身が可逆。 -/
def nerveTransformationPostIso
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    FunctorIso (nerveMap F ≫ L) (nerveMap G ≫ L) := by
  let H := nerveTransformationPostHomotopy η L
  apply functorIsoOfPointwiseInvertibleHomotopy H
  intro z
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective z
  have he : (simplicialHomotopyVertexEdge H (nerveVertex i)).edge =
      ((nerve.edgeMk (η.app i)).map L).edge := by
    change L.app _ ((simplicialHomotopyVertexEdge
      (nerveNatTransHomotopy η) (nerveVertex i)).edge) = _
    exact congrArg (L.app _) (nerveNatTransHomotopy_component η i)
  exact (isInvertibleEdge_congr he).mpr (hη i)

/-- 全同型の順射は、元の全円柱の辺の類そのもの。 -/
theorem nerveTransformationPostIso_hom
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    (nerveTransformationPostIso η L hη).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (nerveTransformationPostHomotopy η L)) := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
