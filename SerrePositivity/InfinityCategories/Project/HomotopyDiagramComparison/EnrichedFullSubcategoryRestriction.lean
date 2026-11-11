module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：豊穣関手を全充満部分圏へ制限し、元の関手と対象の条件の組との同値を構成。
方針：対象に証明を添え、同じ Hom を使う。規約：充填性を仮定しない。
使われ方：cf 対応圏の端点 fiber の厳密な同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable (P : ObjectProperty C)
/-- 元の対象と Hom を保持する全充満部分圏の豊穣包含。 -/
def enrichedFullSubcategoryInclusion : EnrichedFunctor SSet.{u} P.FullSubcategory C where
  obj X := X.obj
  map X Y := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp X Y Z := by
    change eComp SSet X.obj Y.obj Z.obj ≫ 𝟙 _ =
      (𝟙 (X.obj ⟶[SSet] Y.obj) ⊗ₘ 𝟙 (Y.obj ⟶[SSet] Z.obj)) ≫
        eComp SSet X.obj Y.obj Z.obj
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]

variable {A : Type w} [EnrichedCategory SSet.{u} A]
/-- 全対象が条件を満たす元の豊穣関手を、同じ Hom で部分圏へ制限する。 -/
def enrichedFullSubcategoryLift (F : EnrichedFunctor SSet.{u} A C) (h : ∀ a, P (F.obj a)) :
    EnrichedFunctor SSet.{u} A P.FullSubcategory where
  obj a := ⟨F.obj a, h a⟩
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

/-- 豊穣制限と包含の合成は元の関手に一致する。 -/
lemma enrichedFullSubcategoryLift_comp (F : EnrichedFunctor SSet.{u} A C)
    (h : ∀ a, P (F.obj a)) :
    (enrichedFullSubcategoryLift P F h).comp SSet (enrichedFullSubcategoryInclusion P) = F := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp [enrichedFullSubcategoryLift, enrichedFullSubcategoryInclusion, EnrichedFunctor.comp]

/-- 部分圏への豊穣関手と、元の関手および全対象の条件の組との同値。 -/
def enrichedFullSubcategoryFunctorEquiv :
    EnrichedFunctor SSet.{u} A P.FullSubcategory ≃
      {F : EnrichedFunctor SSet.{u} A C // ∀ a, P (F.obj a)} where
  toFun F := ⟨F.comp SSet (enrichedFullSubcategoryInclusion P), fun a ↦ (F.obj a).property⟩
  invFun F := enrichedFullSubcategoryLift P F.val F.property
  left_inv F := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [enrichedFullSubcategoryLift, enrichedFullSubcategoryInclusion, EnrichedFunctor.comp]
  right_inv F := Subtype.ext (enrichedFullSubcategoryLift_comp P F.val F.property)

/-- 豊穣包含との後合成は関手を区別する。 -/
lemma enrichedFullSubcategoryInclusion_comp_injective :
    Function.Injective (fun F : EnrichedFunctor SSet.{u} A P.FullSubcategory ↦
      F.comp SSet (enrichedFullSubcategoryInclusion P)) := by
  intro F G h
  exact (enrichedFullSubcategoryFunctorEquiv P).injective (Subtype.ext h)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
