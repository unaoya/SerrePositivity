module

public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedFamilyFaces

/-!
概要：同じ実初辺を持つ二つの全三角形の、全係数付き実初辺を比較する。
方針：初点を保つ実面の等式を、同じ辺の全 pointed 族へ戻す。
規約：全係数の型を保持。使われ方：最大化の実初辺の指定値を展開せず照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実初辺を持つ二つの全三角形の全係数付き実初辺は、型も含めて一致する。 -/
lemma spaceTrianglePointedFamily_first_heq_of_edge_eq
    (r t : SpaceInfinity.{u} _⦋2⦌) (h : SpaceInfinity.δ 2 r = SpaceInfinity.δ 2 t) :
    HEq ((stdSimplex.δ (2 : Fin 3) ▷ spaceSimplexPointedCoefficients r) ≫
      spaceSimplexPointedFamily r)
      ((stdSimplex.δ (2 : Fin 3) ▷ spaceSimplexPointedCoefficients t) ≫
        spaceSimplexPointedFamily t) := by
  have hf : ∀ {a b : SpaceInfinity.{u} _⦋1⦌}, a = b →
      HEq (spaceSimplexPointedFamily a) (spaceSimplexPointedFamily b) := by
    intro a b hab
    cases hab
    rfl
  exact (heq_of_eq (spaceSimplexPointedFamily_positive_face r (1 : Fin 2))).trans
    ((hf h).trans (heq_of_eq (spaceSimplexPointedFamily_positive_face t (1 : Fin 2))).symm)

end SerrePositivity.InfinityCategories.F2
