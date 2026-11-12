module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramEvaluation

/-!
概要：高次の Hom 全体に関して自然な Kan 値豊穣関手の比較。
方針：評価の可換式を比較の条件にし、二点の図式の strict な変換として実現する。
規約：通常の射だけに関する自然性ではなく、全パラメーターでの自然性を要求する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、edgewise 解像による大域的な coherent な比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：Kan 値豊穣関手の対象での射と全ての Hom に対する自然性の組。
方針：パラメーター付き評価の可換式を条件として部分型に束縛する。
規約：Hom のパラメーターを途中で頂点や同値類へ落とさない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent nerve の関手間の実際の比較を構成する入力。 -/
def KanEnrichedComparison {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :=
  {η : ∀ X, F.obj X ⟶ G.obj X // ∀ X Y,
    ((show (F.obj X).obj ⟶ (G.obj X).obj from η X) ▷ SimplicialCategory.sHom X Y) ≫
      uncurry (G.map X Y) = uncurry (F.map X Y) ≫
        (show (F.obj Y).obj ⟶ (G.obj Y).obj from η Y)}

/-- 概要：豊穣な比較の自然性は任意のパラメーター単体の評価でも成立する。
方針：評価の可換式を制限したパラメーターで評価し、Hom の作用の単体的自然性を使う。
規約：α は単体圏の反対圏の射。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、二点の図式の間の strict な変換の自然性。 -/
lemma kanEnrichedComparison_app {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : KanEnrichedComparison F G)
    (X Y : C) {n k : SimplexCategoryᵒᵖ} (θ : (SimplicialCategory.sHom X Y).obj n)
    (α : n ⟶ k) (x : (F.obj X).obj.obj k) :
    ((G.map X Y).app n θ).app k α ((η.val X).app k x) =
      (η.val Y).app k (((F.map X Y).app n θ).app k α x) := by
  have h := congrArg (fun f : (F.obj X).obj ⊗ SimplicialCategory.sHom X Y ⟶ (G.obj Y).obj ↦
    f.app k (x, (SimplicialCategory.sHom X Y).map α θ)) (η.property X Y)
  have hF := congrArg (fun f : (SimplicialCategory.sHom X Y).obj n ⟶
      ((ihom (F.obj X).obj).obj (F.obj Y).obj).obj k ↦ f θ) ((F.map X Y).naturality α) |>.symm
  have hG := congrArg (fun f : (SimplicialCategory.sHom X Y).obj n ⟶
      ((ihom (G.obj X).obj).obj (G.obj Y).obj).obj k ↦ f θ) ((G.map X Y).naturality α) |>.symm
  change ((ihom (F.obj X).obj).obj (F.obj Y).obj).map α ((F.map X Y).app n θ) =
    (F.map X Y).app k ((SimplicialCategory.sHom X Y).map α θ) at hF
  change ((ihom (G.obj X).obj).obj (G.obj Y).obj).map α ((G.map X Y).app n θ) =
    (G.map X Y).app k ((SimplicialCategory.sHom X Y).map α θ) at hG
  change ((G.map X Y).app k ((SimplicialCategory.sHom X Y).map α θ)).app k (𝟙 k)
      ((η.val X).app k x) =
    (η.val Y).app k (((F.map X Y).app k ((SimplicialCategory.sHom X Y).map α θ)).app k (𝟙 k) x) at h
  rw [← hF, ← hG] at h
  change ((G.map X Y).app n θ).app k (α ≫ 𝟙 k) ((η.val X).app k x) =
    (η.val Y).app k (((F.map X Y).app n θ).app k (α ≫ 𝟙 k) x) at h
  simpa only [Category.comp_id] using h

/-- 概要：豊穣な比較の各対象を一つの射からなる Kan 値図式にする。
方針：比較の射を二点の順序図式として表示する。
規約：零は F、一は G。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較を coherent な二点の図式の族にする対象の作用。 -/
def kanEnrichedComparisonDiagram {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : KanEnrichedComparison F G) (X : C) :
    ULift.{u} (Fin 2) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
    ComposableArrows.mk₁ (η.val X)

/-- 概要：Hom のパラメーター単体から比較の二点図式の間の strict な変換を作る。
方針：零で F の作用、一で G の作用を使い、比較の豊穣自然性で両者を結ぶ。
規約：全ての高次パラメーターを保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較の図式の族の豊穣 Hom の作用。 -/
noncomputable def kanEnrichedComparisonMappingSimplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : KanEnrichedComparison F G)
    (X Y : C) {n : SimplexCategoryᵒᵖ} (θ : (SimplicialCategory.sHom X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex (kanEnrichedComparisonDiagram η X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (kanEnrichedComparisonDiagram η Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) n := by
  refine ⟨(fun i ↦ ?_), ?_⟩
  · rcases i with ⟨i⟩
    refine Fin.cases (motive := fun j : Fin 2 ↦
      ((ihom ((kanEnrichedComparisonDiagram η X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj (ULift.up j))).obj
        ((kanEnrichedComparisonDiagram η Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj (ULift.up j))).obj n)
      ((F.map X Y).app n θ) ?_ i
    intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact (G.map X Y).app n θ
  · intro i j f k α x
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j
    · rfl
    · exact (kanEnrichedComparison_app η X Y θ α x).symm
    · have h := leOfHom f
      change (1 : Fin 2) ≤ 0 at h
      exact (by omega : False).elim
    · rfl

/-- 概要：豊穣な比較は二点図式の strict な変換空間への単体集合の射を与える。
方針：両成分の豊穣関手の Hom の自然性を使う。
規約：始域の Hom の Kan 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な比較を構成する Hom の作用。 -/
noncomputable def kanEnrichedComparisonMappingSpaceMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : KanEnrichedComparison F G) (X Y : C) :
    SimplicialCategory.sHom X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace
      (kanEnrichedComparisonDiagram η X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (kanEnrichedComparisonDiagram η Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) where
  app _ := ↾kanEnrichedComparisonMappingSimplex η X Y
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
