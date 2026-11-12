module
public import SerrePositivity.KST.SConstruction.EnrichedComparisonWhiskers

/-! # 固定した通常射との豊穣合成の全写像
概要：固定した前半・後半の射との合成を Hom 全体の実写像として構成する。
方針：固定頂点の定数族と恒等射の射対を豊穣合成へ渡し、元の全比較辺への作用を計算する。
規約：辺だけでなく全高次単体の実写像を使い、元の全比較辺の像を厳密に保持する。
使われ方：両端固定の BF 回収円柱と高次比較を固定因子との合成へ写す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 固定した第一射との実豊穣合成の全写像。 -/
def enrichedFixedLeftComposition {W X Z : C} (f : W ⟶ X) :
    SimplicialCategory.sHom X Z ⟶ SimplicialCategory.sHom W Z :=
  lift (SSet.const (SimplicialCategory.homEquiv' W X f)) (𝟙 _) ≫
    SimplicialCategory.sHomComp W X Z

/-- 固定した最終射との実豊穣合成の全写像。 -/
def enrichedFixedRightComposition {W Y Z : C} (h : Y ⟶ Z) :
    SimplicialCategory.sHom W Y ⟶ SimplicialCategory.sHom W Z :=
  lift (𝟙 _) (SSet.const (SimplicialCategory.homEquiv' Y Z h)) ≫
    SimplicialCategory.sHomComp W Y Z

/-- 元の左合成比較辺の全区間は、同じ全比較辺を固定因子の合成写像で写した射そのもの。 -/
lemma enrichedComparisonLeftWhisker_map {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (gh : X ⟶ Z)
    (e : (SimplicialCategory.sHom X Z).Edge (SimplicialCategory.homEquiv' _ _ gh)
      (SimplicialCategory.homEquiv' _ _ (g ≫ h))) :
    SSet.yonedaEquiv.symm (enrichedComparisonLeftWhisker f g h gh e).edge =
      SSet.yonedaEquiv.symm e.edge ≫ enrichedFixedLeftComposition f := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change (SimplicialCategory.sHomComp W X Z).app (Opposite.op ⦋1⦌)
    ((SSet.Edge.id (SimplicialCategory.homEquiv' W X f)).edge, e.edge) =
      (SimplicialCategory.sHomComp W X Z).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' W X f) 1, e.edge)
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' W X f) 1 =
    (SSet.Edge.id (SimplicialCategory.homEquiv' W X f)).edge from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _]

/-- 元の右合成比較辺の全区間も、同じ全比較辺を固定因子の合成写像で写した射そのもの。 -/
lemma enrichedComparisonRightWhisker_map {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y)
    (e : (SimplicialCategory.sHom W Y).Edge (SimplicialCategory.homEquiv' _ _ fg)
      (SimplicialCategory.homEquiv' _ _ (f ≫ g))) :
    SSet.yonedaEquiv.symm (enrichedComparisonRightWhisker f g h fg e).edge =
      SSet.yonedaEquiv.symm e.edge ≫ enrichedFixedRightComposition h := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change (SimplicialCategory.sHomComp W Y Z).app (Opposite.op ⦋1⦌)
    (e.edge, (SSet.Edge.id (SimplicialCategory.homEquiv' Y Z h)).edge) =
      (SimplicialCategory.sHomComp W Y Z).app (Opposite.op ⦋1⦌)
        (e.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' Y Z h) 1)
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' Y Z h) 1 =
    (SSet.Edge.id (SimplicialCategory.homEquiv' Y Z h)).edge from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _]

end SerrePositivity.KST.SConstruction
