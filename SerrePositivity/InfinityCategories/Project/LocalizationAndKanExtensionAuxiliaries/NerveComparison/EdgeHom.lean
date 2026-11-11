module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTrans

/-!
概要：端点の表示を揃えた辺の類の比較と nerve の後合成の式。
方針：端点の等式を消去して辺の値を比較し、nerve の単体公式を使う。
規約：指定された辺と通常の射を選び直さない。
使われ方：自然変換の nerve 表示と whiskering の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：端点と辺の値が一致すれば端点を揃えた辺の類は等しい。
方針：端点の等式を消去し、辺の外延性を使う。
規約：辺の類を h の射として比較する。
使われ方：単体の値の等式から端点輸送つきの自然変換の等式へ移す。 -/
lemma homMk_congr {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') (e : SSet.Edge x y) (e' : SSet.Edge x' y')
    (he : e.edge = e'.edge) :
    eqToHom (congrArg HomotopyCategory.mk hx).symm ≫ HomotopyCategory.homMk e ≫
      eqToHom (congrArg HomotopyCategory.mk hy) = HomotopyCategory.homMk e' := by
  cases hx
  cases hy
  have h : e = e' := SSet.Edge.ext he
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：nerve の辺の類の後合成は通常の射の後合成の辺の類と一致する。
方針：nerveMap の零次と一次の単体公式を端点つきの辺の比較へ渡す。
規約：端点は元の射の像であり、等式で表示を揃える。
使われ方：通常の前後合成関手の h nerve 上での自然性。 -/
lemma nerveEdgeHom_map {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) {x y : C} (f : x ⟶ y) :
    eqToHom (congrArg HomotopyCategory.mk (nerveMap_app_mk₀ F x)).symm ≫
      HomotopyCategory.homMk ((nerve.edgeMk f).map (nerveMap F)) ≫
        eqToHom (congrArg HomotopyCategory.mk (nerveMap_app_mk₀ F y)) =
      HomotopyCategory.homMk (nerve.edgeMk (F.map f)) := by
  exact homMk_congr (nerveMap_app_mk₀ F x) (nerveMap_app_mk₀ F y) _ _
    (nerveMap_app_mk₁ F f)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
