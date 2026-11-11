module
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DeformationLocalization
/-!
概要：指定変形比較を反転する関手について、同じ包含上の制限からの実降下比較を得る。
方針：元の全単体ホモトピーを後合成し、各実成分辺の反転から全関手同型を作る。
規約：局所化の存在や対象成分だけの一致を仮定しない。使われ方：K-flat kernel の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
/-- 元の変形比較の全成分を反転する実関手は、同じ包含制限から全関手同型で回収される。 -/
def deformationFunctorDescentIso {X D Y : SSet.{u}} [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (W : Set (X _⦋1⦌))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ W)
    (T : X ⟶ Y) (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges T W) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ I ≫ T) T := by
  let H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H T
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy H' (by
    intro x
    have hi := hT (hH x)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := Y)
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' x).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge).map
        ((truncation 2).map T)) rfl).mpr hi)
  simpa only [Category.assoc, Category.id_comp] using! he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
