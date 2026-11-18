module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.RestrictedSectionsLocalEquivalenceLimit

/-!
概要：局所同値に沿う元の指定切断の辺は任意の準圏係数で可逆。
方針：指定極限錐の制限の極限性を同じ辺の可逆性へ戻す。
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

/-- 局所同値に沿う元の指定切断の辺は任意の準圏係数で可逆。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の集合値前層の局所同値。"]
lemma sections_localEquiv_iso :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C E) (hO : IsSheaf J O)
  (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)),
  IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated := by
  intro C hC E hQC J P Q φ hφ O hO hP hQ
  exact (sectionsMap_isInvertible_iff φ O (sectionsOfCone P O hP) (sectionsOfCone_isLimit P O hP)
    (sectionsOfCone Q O hQ) (sectionsOfCone_isLimit Q O hQ)).mpr
      (restrictSectionsCone_isLimit_of_localEquiv J φ hφ O hO
        (sectionsOfCone Q O hQ) (sectionsOfCone_isLimit Q O hQ))

end SerrePositivity.InfinityCategories.Sheaves
