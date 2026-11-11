module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial

/-!
概要：全高次の Hom に関して自然な quasicategory 値豊穣関手の比較。
方針：元のパラメーター付き評価の可換式を比較の条件とし、任意の次数の評価を回収する。
規約：値に Kan 性を要求せず、元の全関手空間の作用を保持する。
使われ方：Cat∞ 値分類の底変換比較を全 fibration の coherent な族へ束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- quasicategory 値豊穣関手の全対象での比較と、元の全高次 Hom の評価に関する自然性。 -/
def QuasicategoryEnrichedComparison {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}) :=
  {η : ∀ X, (F.obj X).obj ⟶ (G.obj X).obj // ∀ X Y,
    (η X ▷ SimplicialCategory.sHom X Y) ≫ uncurry (G.map X Y) =
      uncurry (F.map X Y) ≫ η Y}

/-- 同じ比較の自然性は、任意の次数・任意のパラメーター制限で成立する。 -/
lemma quasicategoryEnrichedComparison_app
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}}
    (η : QuasicategoryEnrichedComparison F G) (X Y : C)
    {n k : SimplexCategoryᵒᵖ} (θ : (SimplicialCategory.sHom X Y).obj n)
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

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
