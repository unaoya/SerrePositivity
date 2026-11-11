module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionMappingPair
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceHom

/-!
概要：相対始点の境界充填と全パラメータの射の制限の全単射。
方針：元の pinched 写像空間の比較を h Fun の射の作用へ移す。
規約：指定頂点から出る射だけを量化する。
使われ方：左随伴による幾何学的実現の保存。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：始点境界充填は指定始点から出る h の射の作用を全単射にする。
方針：pinched 比較の同値性を元のホモトピー圏の射の作用へ移す。
規約：同じ射と端点を保持する。
使われ方：余極限余錐の全射の制限。 -/
lemma homMap_bijective_of_initialBoundaryLifting {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B)
    (x : E _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x) (y : E _⦋0⦌) :
    Function.Bijective ((hoFunctor.map p).toFunctor.map :
      (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) → _) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary p x y hx
  have hm : ((hoFunctor.map p).toFunctor.map :
      (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) → _) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingSpaceHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) := by
    funext α
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingSpaceHomMap_functor p x y α).symm
  rw [hm]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingSpaceHomMap_bijective _ he

/-- 概要：定値パラメータ族の全射の制限が全単射なら元の相対始点は境界充填を持つ。
方針：全端点との pinched 比較を全パラメータ判定で同値にする。
規約：元の始点関手を固定する。
使われ方：随伴の Hom 対応から余極限性へ戻す。 -/
lemma initialBoundaryLifting_pre_of_constantFamilyHom
    {K B X : SSet.{u}} [Quasicategory X] (δ : K ⟶ B) [Mono δ] (F : B ⟶ X)
    (h : ∀ (A : SSet.{u}) (G : B ⟶ X), Function.Bijective
      ((hoFunctor.map ((pre δ).app ((ihom A).obj X))).toFunctor.map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X) (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X) → _)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting ((pre δ).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanInitialBoundaryLifting_of_relativeInitial
  intro y
  obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B X).surjective y
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precomposition_pinchedHomMap_equivalence_of_constantFamily δ F G (fun A ↦ h A G)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
