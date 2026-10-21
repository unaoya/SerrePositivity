module
public import SerrePositivity.InfinityCategories.F1B.Adjunction
public import Mathlib.CategoryTheory.Comma.Arrow
/-!
概要：指定随伴を関手の等式で輸送しても、余単位の Arrow 表示を保つ。
方針：両端の指定等式と同じ随伴の HEq を使う。
規約：元の余単位を保持する。使われ方：kernel 随伴の厳密回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- 指定随伴の同じ余単位を、両端輸送に依存しない Arrow として回収する。 -/
lemma QCatAdjunction.counitHom_arrow_of_heq
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F F' : X ⟶ Y} {G G' : Y ⟶ X}
    (a : QCatAdjunction F G) (a' : QCatAdjunction F' G')
    (hf : F = F') (hg : G = G') (h : HEq a a') :
    Arrow.mk a.counitHom = Arrow.mk a'.counitHom := by
  subst F' G'
  cases eq_of_heq h
  rfl
end SerrePositivity.InfinityCategories
