module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionCoordinates

/-!
概要：同じ実 Hom の端点表示変更の二段合成を、同じ一段の表示変更へ揃える。
方針：対象の等号を消去し、元の Hom の射を保つ。
規約：係数や射を取り替えない。使われ方：実 prism の Hom の端点正規化の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実 Hom の二段の端点表示変更は、合成した端点同定による表示変更。 -/
lemma simplicialHom_display_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {T : SSet.{u}} {A B A' B' A'' B'' : C} (f : T ⟶ SimplicialCategory.sHom A B)
    (hA : A = A') (hB : B = B') (kA : A' = A'') (kB : B' = B'') :
    (f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom kA kB) =
    f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (hA.trans kA) (hB.trans kB)) := by
  cases hA; cases hB; cases kA; cases kB
  simp only [eqToHom_refl, Category.comp_id]

/-- 同じ端点表示への移送後の一致から、元の Hom 比較の一致を反映する。 -/
lemma simplicialHom_eq_of_display {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {T : SSet.{u}} {A B A' B' A'' B'' : C} (f : T ⟶ SimplicialCategory.sHom A B)
    (g : T ⟶ SimplicialCategory.sHom A' B') (hA : A = A') (hB : B = B')
    (kA : A' = A'') (kB : B' = B'')
    (h : f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (hA.trans kA) (hB.trans kB)) =
      g ≫ eqToHom (congrArg₂ SimplicialCategory.sHom kA kB)) :
    f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) = g := by
  apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom kA kB))).mp
  rw [simplicialHom_display_comp f hA hB kA kB]
  exact h

end SerrePositivity.InfinityCategories.F2
