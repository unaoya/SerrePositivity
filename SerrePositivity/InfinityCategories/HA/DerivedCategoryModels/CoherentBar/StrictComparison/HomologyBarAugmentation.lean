module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarSimplicial

/-!
概要：ホモロジー図式の simplicial bar を同じ strict 余極限へ増大する。
方針：各始点係数の余極限の脚を直和から貼り、余錐の自然性を使う。
規約：この葉はホモロジー加群の通常の図式にのみ適用する。
使われ方：filtered 完全性による増大 bar のホモロジー計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [Category.{u} J]
  (F : J ⥤ ModuleCat.{u} R) (c : Cocone F)

def dgHomologyBarAugmentationComponent (Δ : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F).obj Δ ⟶ c.pt :=
  Sigma.desc (fun s => c.ι.app (s.obj 0))

@[reassoc (attr := simp)]
lemma dgHomologyBarAugmentationComponent_ι (Δ : SimplexCategoryᵒᵖ)
    (s : (nerve J).obj Δ) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F Δ) s ≫ dgHomologyBarAugmentationComponent R F c Δ =
      c.ι.app (s.obj 0) := by
  simp only [dgHomologyBarAugmentationComponent, Sigma.ι_comp_desc]

def dgHomologyBarAugmentation :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F ⟶ (SimplicialObject.const (ModuleCat R)).obj c.pt where
  app Δ := dgHomologyBarAugmentationComponent R F c Δ
  naturality Δ Γ α := by
    apply Sigma.hom_ext
    intro s
    erw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarMap_ι, Category.assoc,
      dgHomologyBarAugmentationComponent_ι]
    simp only [Functor.const_obj_map, Category.comp_id]
    erw [dgHomologyBarAugmentationComponent_ι]
    exact c.w (s.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0))))

def dgHomologyBarAugmented : SimplicialObject.Augmented (ModuleCat R) where
  left := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F
  right := c.pt
  hom := dgHomologyBarAugmentation R F c

abbrev dgHomologyBarColimitAugmented : SimplicialObject.Augmented (ModuleCat R) :=
  dgHomologyBarAugmented R F (colimit.cocone F)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
