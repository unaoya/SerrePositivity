module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.OverEquivalenceLimitComposition

/-!
概要：元の離散重みの値比較の中の、指定切断錐とleft全空間の極限の比較を固定する。
方針：元の定義と同じ要素の圏の比較・射影の等式・指定極限錐をそのまま使う。
規約：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）の既存の比較の計算法則。
使われ方：S8 の固定されたweightedSections_discreteで、途中の極限の選択を照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の離散値比較の定義内の、同じ指定切断錐からleft全空間の極限への比較。 -/
def discreteSectionsLeftComparison (O : Presheaf C E) (P : Cᵒᵖ ⥤ Type u)
    (hP : HasLimit (sectionsOfDiagram P O))
    (d : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection (discretePresheaf P)) ≫ O))
    (hd : IsLimitCone d) : VertexIso (sectionsOf P O hP) d.vertex := by
  have ha : IsQCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.elementsComparisonNatural P)) :=
    IsQCatEquivalence.ulift.{u, u + 1}
      (SetWeight.elementsComparisonNatural_isPrecompositionEquivalence P).isQCatEquivalence
  have hp : (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.elementsComparisonNatural P) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (smallLeftUnstraighteningProjection (discretePresheaf P)) =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π P)) := by
    rw [← Functor.map_comp]
    exact congrArg ((SSet.uliftFunctor.{u + 1, u}).map)
      (SetWeight.elementsComparisonNatural_projection P)
  exact limitVertexIsoOfOverEquivalence
    ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.elementsComparisonNatural P)) ha hp O
    (sectionsOfCone P O hP) d (sectionsOfCone_isLimit P O hP) hd

/-- 元の比較に標的の標準極限比較を後合成しても、同じ比較になる。 -/
lemma discreteSectionsLeftComparison_hom_comp (O : Presheaf C E) (P : Cᵒᵖ ⥤ Type u)
    (hP : HasLimit (sectionsOfDiagram P O))
    (d e : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection (discretePresheaf P)) ≫ O))
    (hd : IsLimitCone d) (he : IsLimitCone e) :
    (discreteSectionsLeftComparison O P hP d hd).hom ≫ (limitVertexIso d e hd he).hom =
      (discreteSectionsLeftComparison O P hP e he).hom := by
  unfold discreteSectionsLeftComparison
  apply limitVertexIsoOfOverEquivalence_hom_comp

end SerrePositivity.InfinityCategories.Sheaves
