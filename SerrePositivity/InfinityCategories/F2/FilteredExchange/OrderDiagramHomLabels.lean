module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.MorphismInitialTail

/-!
概要：元の順序図式の Hom を、指定した同じ時刻の端点表示へ移す。
方針：既存の定値 Hom の式と薄い圏の射の移送則を合成する。
規約：選んだ射を取り替えない。使われ方：実 prism の tail と head の全 Hom 照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ時刻の端点表示へ移した Hom は、同じ指定順序射の像への定値射。 -/
lemma orderDiagramEnrichedHom_label_transport {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (β : J →o Fin 2) (D : Fin 2 ⥤ C) (i j : SimplicialThickening J)
    (hij : i.as ≤ j.as) (k l : Fin 2) (hk : β i.as = k) (hl : β j.as = l)
    (hkl : k ≤ l) :
    orderDiagramEnrichedHom (β.toFunctor ⋙ D) i j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg D.obj hk) (congrArg D.obj hl)) =
      SSet.const (SimplicialCategory.homEquiv' _ _ (D.map (homOfLE hkl))) := by
  rw [orderDiagramEnrichedHom_const (β.toFunctor ⋙ D) i j hij, SSet.const_comp]
  apply congrArg SSet.const
  change (eqToHom (congrArg₂ SimplicialCategory.sHom
    (congrArg D.obj hk) (congrArg D.obj hl))).app (Opposite.op ⦋0⦌)
    (SimplicialCategory.homEquiv' _ _ (D.map (homOfLE (β.monotone hij)))) = _
  rw [simplicialHomVertex_transport (congrArg D.obj hk) (congrArg D.obj hl)]
  apply congrArg (SimplicialCategory.homEquiv' _ _)
  exact functor_map_transport_of_isThin D hk hl _ (homOfLE hkl)

end SerrePositivity.InfinityCategories.F2
