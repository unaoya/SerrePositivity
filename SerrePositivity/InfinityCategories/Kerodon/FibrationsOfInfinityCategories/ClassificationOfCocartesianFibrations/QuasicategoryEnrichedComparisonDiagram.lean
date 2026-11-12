module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory

/-!
概要：全 Hom に自然な quasicategory 値の比較を二点図式の全変換の族へ写す。
方針：比較の両成分の豊穣作用を使い、元の全パラメーターの自然性で結ぶ。
規約：図式の変換空間の充填性を要求しない。
使われ方：底変換比較の全 fibration に関する coherent な実現の入力。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：豊穣な比較の各対象を一つの射からなる quasicategory 値図式にする。
方針：比較の射を二点の順序図式として表示する。
規約：零は F、一は G。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較を coherent な二点の図式の族にする対象の作用。 -/
def quasicategoryEnrichedComparisonDiagram {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G) (X : C) :
    ULift.{u} (Fin 2) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
    ComposableArrows.mk₁ (η.val X)

/-- 概要：Hom のパラメーター単体から比較の二点図式の間の strict な変換を作る。
方針：零で F の作用、一で G の作用を使い、比較の豊穣自然性で両者を結ぶ。
規約：全ての高次パラメーターを保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較の図式の族の豊穣 Hom の作用。 -/
noncomputable def quasicategoryEnrichedComparisonMappingSimplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G)
    (X Y : C) {n : SimplexCategoryᵒᵖ} (θ : (SimplicialCategory.sHom X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex (quasicategoryEnrichedComparisonDiagram η X ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)
      (quasicategoryEnrichedComparisonDiagram η Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) n := by
  refine ⟨(fun i ↦ ?_), ?_⟩
  · rcases i with ⟨i⟩
    refine Fin.cases (motive := fun j : Fin 2 ↦
      ((ihom ((quasicategoryEnrichedComparisonDiagram η X ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget).obj (ULift.up j))).obj
        ((quasicategoryEnrichedComparisonDiagram η Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget).obj (ULift.up j))).obj n)
      ((F.map X Y).app n θ) ?_ i
    intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact (G.map X Y).app n θ
  · intro i j f k α x
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j
    · rfl
    · exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedComparison_app η X Y θ α x).symm
    · have h := leOfHom f
      change (1 : Fin 2) ≤ 0 at h
      exact (by omega : False).elim
    · rfl

/-- 概要：豊穣な比較は二点図式の strict な変換空間への単体集合の射を与える。
方針：両成分の豊穣関手の Hom の自然性を使う。
規約：始域の Hom の Kan 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な比較を構成する Hom の作用。 -/
noncomputable def quasicategoryEnrichedComparisonMappingSpaceMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G) (X Y : C) :
    SimplicialCategory.sHom X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace
      (quasicategoryEnrichedComparisonDiagram η X ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)
      (quasicategoryEnrichedComparisonDiagram η Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) where
  app _ := ↾quasicategoryEnrichedComparisonMappingSimplex η X Y
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro θ
    apply Subtype.ext
    funext i
    rcases i with ⟨i⟩
    fin_cases i
    · exact congrArg (fun f : (SimplicialCategory.sHom X Y).obj n ⟶
        ((ihom (F.obj X).obj).obj (F.obj Y).obj).obj m ↦ f θ) ((F.map X Y).naturality α)
    · exact congrArg (fun f : (SimplicialCategory.sHom X Y).obj n ⟶
        ((ihom (G.obj X).obj).obj (G.obj Y).obj).obj m ↦ f θ) ((G.map X Y).naturality α)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
