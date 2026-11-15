module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafOppositeRightKanCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeCommaEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitExistence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits

/-!
概要：一般の空間値重みの切断を、反対 Yoneda に沿う実右 Kan 延長として構成する。
方針：既存の小さい元の圏との比較で局所図式の極限を取り、右 Kan 存在定理を使う。
使われ方：HTT 5.1.5.6、Kerodon §8.4（Tag 03V7）の重み付き切断。
規約：標的には小極限だけを使い、大きい局所形状の極限を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 1}} [Quasicategory E]

/-- 反対 Yoneda の局所図式は、小さい元の圏によって極限を持つ。 -/
lemma nativeWeightedSectionsDiagram_hasLimit
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}) :
    HasLimit (rightKanDiagram (SSet.opFunctor.map (yonedaInfinityMap A)) O
      (SSet.opObjEquiv.symm (functorVertex P))) := by
  let j := (uliftOppositeIso.{u, u + 1} (smallRightUnstraightening P)).hom ≫
    presheafElementsRightKanComparison P
  have hj : IsQCatEquivalence j :=
    (qCatEquivalenceOfIso (uliftOppositeIso.{u, u + 1} (smallRightUnstraightening P))).isQCatEquivalence.comp
      (presheafElementsRightKanComparison_isQCatEquivalence P)
  apply hasLimit_of_equivalentRestriction j hj
  exact hE.hasLimit _

/-- 小極限の存在から、全空間値重みに対する同じ右 Kan 延長が存在する。 -/
lemma exists_nativeWeightedSections
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E) :
    ∃ (G : (PresheafInfinity A).op ⟶ E)
      (ε : SSet.Homotopy (SSet.opFunctor.map (yonedaInfinityMap A) ≫ G) O),
      IsRightKanExtension (SSet.opFunctor.map (yonedaInfinityMap A)) O G ε := by
  apply exists_kanRightExtension_of_local_limits
  intro v
  obtain ⟨v, rfl⟩ := SSet.opObjEquiv.symm.surjective v
  obtain ⟨P, rfl⟩ := (presheafInfinityObjectEquiv A).surjective v
  exact nativeWeightedSectionsDiagram_hasLimit hE O P

end SerrePositivity.InfinityCategories.Sheaves
