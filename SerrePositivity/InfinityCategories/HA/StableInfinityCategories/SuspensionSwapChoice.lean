module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSwapNaturality
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyPreadditive

/-! # Suspension の交換作用の選択変更

概要：交換作用が負の恒等射であるという主張は suspension の選択に依存しない。
方針：標準比較との自然性を用い、その同型を右から消す。
規約：負号そのものを証明する定理ではない。使われ方：対称な模型での符号を任意の suspension へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories


/-- 概要：交換作用は同じ始点の suspension の標準比較と可換。
方針：一般の図式の射に対する自然性を標準比較へ適用する。
規約：安定性や加法性は不要。使われ方：符号の選択変更。 -/
lemma SuspensionSquare.swapIso_comparison {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (s.comparisonIso r).hom ≫ r.swapIso.hom =
      s.swapIso.hom ≫ (s.comparisonIso r).hom :=
  s.swapIso_naturality r (s.diagramComparisonIso r).hom

section
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
local instance : Preadditive X.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho (X := X)

/-- 概要：一つの suspension で交換が負の恒等射なら、同じ始点の任意の suspension でも成り立つ。
方針：標準比較との可換性に符号を代入し、同型で打ち消す。
規約：安定性により既存の加法構造を使う。使われ方：対称な模型から一般の選択への符号の転送。 -/
lemma SuspensionSquare.swapIso_eq_neg_id_of_comparison
    {x : X _⦋0⦌}
    (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x)
    (hr : r.swapIso.hom = -𝟙 (SSet.HomotopyCategory.mk r.vertex : hoFunctor.obj X)) :
    s.swapIso.hom = -𝟙 (SSet.HomotopyCategory.mk s.vertex : hoFunctor.obj X) := by
  apply (cancel_mono (s.comparisonIso r).hom).1
  rw [← s.swapIso_comparison r, hr]
  simp

end

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
