module
public import SerrePositivity.KST.Fibration.RelativeDiagramCore

/-! # 成分ごとの弱同値による単体的図式

単体的図式の各段に評価族があり、その再添字が実射と可換ならば、相対部分複体は
元の全ての面・退化を持つ単体的対象になる。具体的 S• の界面への接続に用いる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

variable {B C : SSet.{u}} (q : B ⟶ C) (F : SimplicialObject SSet.{u})
  (J : SimplexCategory ⥤ Type v)
  (ev : ∀ n, J.obj n.unop → (F.obj n ⟶ B))
  (he : ∀ {n m} (α : n ⟶ m) (j : J.obj m.unop),
    F.map α ≫ ev m j = ev n (J.map α.unop j))

/-- 各段の全指定成分で弱同値となる単体からなる単体的対象。 -/
def relativeSimplicialDiagram : SimplicialObject SSet.{u} where
  obj n := (relativeDiagram q (ev n) : SSet.{u})
  map α := relativeDiagramMap q (ev _) (ev _) (F.map α) (J.map α.unop) (he α)
  map_id n := by
    apply (cancel_mono (relativeDiagram q (ev n)).ι).1
    simp only [relativeDiagramMap_ι, F.map_id, Category.comp_id, Category.id_comp]
  map_comp α β := by
    apply (cancel_mono (relativeDiagram q (ev _)).ι).1
    simp only [Category.assoc, relativeDiagramMap_ι, F.map_comp]
    simp only [← Category.assoc, relativeDiagramMap_ι]

/-- 元の単体的図式への包含。 -/
def relativeSimplicialDiagramInclusion : relativeSimplicialDiagram q F J ev he ⟶ F where
  app n := (relativeDiagram q (ev n)).ι
  naturality {_n _m} α := relativeDiagramMap_ι q _ _ _ _ (he α)

/-- 各段の core からの包含も全ての面・退化と可換。 -/
def relativeSimplicialDiagramCoreInclusion :
    F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor ⟶ relativeSimplicialDiagram q F J ev he where
  app n := relativeDiagramCoreInclusion q (ev n)
  naturality {_n _m} α := (relativeDiagramCoreInclusion_naturality q _ _ _ _ (he α)).symm

end SerrePositivity.KST.Fibration
