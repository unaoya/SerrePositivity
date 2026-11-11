module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QuasicategoryEnrichedComparisonDiagram

/-!
概要：高次の Hom に関して自然な比較を二点図式の豊穣的な族にする。
方針：比較の変換空間への作用を使い、両端の豊穣関手の単位・合成則を成分で適用する。
規約：端点の評価で二つの豊穣関手を厳密に回収する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、自然な比較から coherent nerve の写像の比較を構成する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：豊穣な比較は二点の quasicategory 値図式への豊穣関手を与える。
方針：比較の二点図式を対象の作用とし、strict な変換空間への射を Hom の作用とする。
規約：始域の局所 Kan 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較を coherent な図式の族として実現する入力。 -/
noncomputable def quasicategoryEnrichedComparisonArrowEnriched {C : Type v}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G) :
    EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramObject (ULift.{u} (Fin 2))) where
  obj X := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.quasicategoryEnrichedComparisonDiagram η X, trivial⟩
  map X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.quasicategoryEnrichedComparisonMappingSpaceMap η X Y
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    funext i
    rcases i with ⟨i⟩
    fin_cases i
    · exact congrArg (fun f : 𝟙_ SSet.{u} ⟶ (ihom (F.obj X).obj).obj (F.obj X).obj ↦
        f.app n t) (F.map_id X)
    · exact congrArg (fun f : 𝟙_ SSet.{u} ⟶ (ihom (G.obj X).obj).obj (G.obj X).obj ↦
        f.app n t) (G.map_id X)
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    have hcomp (H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}) :
        (H.map X Z).app n ((eComp SSet X Y Z).app n (f, g)) =
          CategoryTheory.Functor.HomObj.comp ((H.map X Y).app n f) ((H.map Y Z).app n g) := by
      have h := congrArg (fun m : SimplicialCategory.sHom X Y ⊗ SimplicialCategory.sHom Y Z ⟶
        (ihom (H.obj X).obj).obj (H.obj Z).obj ↦ m.app n (f, g)) (H.map_comp X Y Z)
      apply CategoryTheory.Functor.functorHom_ext
      intro k α
      apply ConcreteCategory.hom_ext
      intro x
      have h' := congrArg (fun θ : ((ihom (H.obj X).obj).obj (H.obj Z).obj).obj n ↦
        θ.app k α x) h
      change ((H.map X Z).app n ((eComp SSet X Y Z).app n (f, g))).app k α x =
        ((H.map Y Z).app n g).app k (α ≫ 𝟙 k)
          (((H.map X Y).app n f).app k (α ≫ 𝟙 k) x) at h'
      rw [Category.comp_id] at h'
      exact h'
    apply Subtype.ext
    funext i
    rcases i with ⟨i⟩
    fin_cases i
    · exact hcomp F
    · exact hcomp G

/-- 概要：比較の二点図式の豊穣的な族を零で評価すると F を回収する。
方針：対象と Hom の零側の成分を計算する。
規約：等式は豊穣関手の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な比較の始点条件。 -/
lemma quasicategoryEnrichedComparisonArrowEnriched_zero {C : Type v}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G) :
    (quasicategoryEnrichedComparisonArrowEnriched η).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramEvaluationEnriched (ULift.up (0 : Fin 2))) = F := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 概要：比較の二点図式の豊穣的な族を一で評価すると G を回収する。
方針：対象と Hom の一側の成分を計算する。
規約：等式は豊穣関手の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な比較の終点条件。 -/
lemma quasicategoryEnrichedComparisonArrowEnriched_one {C : Type v}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G) :
    (quasicategoryEnrichedComparisonArrowEnriched η).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramEvaluationEnriched (ULift.up (1 : Fin 2))) = G := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
