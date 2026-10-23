module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedFamily
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexSourceConeFaces

/-!
概要：全 Hom を係数とする実 pointed 族を、元の初点を保つ面へ厳密に制限する。
方針：元の source coslice の実 Yoneda 射の面の等式を、同じ全前合成へ入れる。
規約：独立の全係数は固定し、図式の面だけを制限する。
使われ方：三角形の二つの面を同じ全 Hom 比較の族として照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の初点を保つ面では、coslice の全 Hom 族も元の面の族に厳密に等しい。 -/
lemma spaceSimplexCoslicePointedFamily_positive_face {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌) (i : Fin (n + 1)) :
    (stdSimplex.δ i.succ ▷ _) ≫ spaceSimplexCoslicePointedFamily s =
      spaceSimplexCoslicePointedFamily (SpaceInfinity.δ i.succ s) := by
  unfold spaceSimplexCoslicePointedFamily
  rw [← Category.assoc, ← comp_whiskerRight, spaceSimplexSourceCone_map_positive_face]
  rfl

/-- 元の実 pointed 族の面でも、同じ独立の全 Hom 係数と全図式の面を保持する。 -/
lemma spaceSimplexPointedFamily_positive_face {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌) (i : Fin (n + 1)) :
    (stdSimplex.δ i.succ ▷ _) ≫ spaceSimplexPointedFamily s =
      spaceSimplexPointedFamily (SpaceInfinity.δ i.succ s) := by
  rw [spaceSimplexPointedFamily, ← Category.assoc,
    spaceSimplexCoslicePointedFamily_positive_face]
  rfl

end SerrePositivity.InfinityCategories.F2
