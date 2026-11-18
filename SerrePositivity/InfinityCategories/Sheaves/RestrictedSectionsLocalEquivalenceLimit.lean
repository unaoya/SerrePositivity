module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.RepresentableRestrictedSectionsLimit

/-!
概要：局所同値に沿った元の指定切断錐の制限は極限錐。
方針：同じ錐のすべての共変表現可能値での極限性を反映する。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）。
使われ方：集合値局所同値に沿う指定切断の可逆性。
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
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 局所同値に沿った元の指定切断錐の制限は極限錐。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の集合値前層の局所同値。"]
lemma restrictSectionsCone_isLimit_of_localEquiv :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C E) (hO : IsSheaf J O)
  (c : JoinCone (sectionsOfDiagram Q O)) (hc : IsLimitCone c),
  IsLimitCone (SetWeight.restrictSectionsCone φ O c) := by
  intro C hC E hQC J P Q φ hφ O hO c hc
  exact isLimitCone_of_covariantRepresentableInfinity (SetWeight.restrictSectionsCone φ O c)
    (representable_restrictedSectionsCone_isLimit J φ hφ O hO c hc)

end SerrePositivity.InfinityCategories.Sheaves
