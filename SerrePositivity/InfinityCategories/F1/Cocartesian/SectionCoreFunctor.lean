module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionsCoreRestriction
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomNaturality

/-!
概要：底上の図式に対する cocartesian section の core を反変な Kan 値関手へ束ねる。
方針：元の section の制限に core 関手を適用し、厳密な恒等・合成を保つ。
規約：任意の底上の単射に沿う遷移は、実際の同じ core 制限の Kan fibration。
使われ方：Hom 比較を境界・骨格で貼り合わせる Kan 値の制限図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

/-- 元の cocartesian section の core と全ての底上の制限を、反変な Kan 値関手へ束ねる。 -/
def cocartesianSectionCoreFunctor {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] :
    (Over B)ᵒᵖ ⥤ KanObject.{u} where
  obj a := ⟨(quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p a.unop.hom) : SSet.{u}), inferInstance⟩
  map i := quasicategoryCoreMap (SerrePositivity.InfinityCategories.cocartesianSectionsPre p i.unop)
  map_id a := by
    change quasicategoryCoreMap (SerrePositivity.InfinityCategories.cocartesianSectionsPre p (𝟙 a.unop)) = 𝟙 _
    rw [SerrePositivity.InfinityCategories.cocartesianSectionsPre_id]
    exact quasicategoryCoreFunctor.map_id _
  map_comp f g := by
    change quasicategoryCoreMap (SerrePositivity.InfinityCategories.cocartesianSectionsPre p (g.unop ≫ f.unop)) =
      quasicategoryCoreMap (SerrePositivity.InfinityCategories.cocartesianSectionsPre p f.unop) ≫
        quasicategoryCoreMap (SerrePositivity.InfinityCategories.cocartesianSectionsPre p g.unop)
    rw [← SerrePositivity.InfinityCategories.cocartesianSectionsPre_comp]
    exact quasicategoryCoreFunctor.map_comp _ _

/-- この同じ制限図式の遷移を単射に沿って取ると、実際の Kan fibration を得る。 -/
lemma cocartesianSectionCoreFunctor_map_fibration
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] :
    Fibration (((cocartesianSectionCoreFunctor p) ⋙ kanObjectForget).map i.op) :=
  core_kanCocartesianSectionsPre_fibration p i

end SerrePositivity.InfinityCategories
