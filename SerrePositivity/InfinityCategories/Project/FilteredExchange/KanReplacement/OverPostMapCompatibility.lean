module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：Over 圏への関手の後合成と、底の射に沿う後合成は厳密に可換。
方針：元の関手の合成保存と Over の対象・射の外延性を使う。
規約：自然同型だけでなく関手の等式を証明する。
使われ方：Bousfield–Kan 重みの添字関手に関する自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：関手による Over の写像は底の射の後合成と可換。
方針：対象の構造射で U の合成保存を使い、射の左成分を比較する。
規約：同じ宇宙の任意の小圏。使われ方：反変重みの自然変換。 -/
lemma overPost_map_eq {I J : Type u} [SmallCategory I] [SmallCategory J] (U : J ⥤ I)
    {i j : J} (f : i ⟶ j) :
    Over.map f ⋙ Over.post U = Over.post U ⋙ Over.map (U.map f) := by
  refine CategoryTheory.Functor.ext (fun a ↦ ?_) ?_
  · change Over.mk (U.map (a.hom ≫ f)) = Over.mk (U.map a.hom ≫ U.map f)
    rw [U.map_comp]
  · intro a b g
    apply Over.OverMorphism.ext
    simp [Over.eqToHom_left]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
