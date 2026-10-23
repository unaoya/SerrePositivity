module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionTetrahedronZeroFamily
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionTetrahedronPointedFace

/-!
概要：零面の実最後辺を、元の全三角形の同じ実最後辺へ厳密に戻す。
方針：元の比較三単体の零面と第一面に共有される同じ辺を使う。
規約：全初点係数を保持。使われ方：零面の指定比較と元の最後辺の指定比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "A" => spaceSimplexPointedCoefficients s

/-- 零面の実最後辺は、元の全三角形の同じ実最後辺そのもの。 -/
lemma spaceCompositionZeroFamily_last_eq_original :
    (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ spaceCompositionTetrahedronZeroFamily s =
      (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ spaceSimplexPointedFamily s := by
  have h : stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) =
      stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [spaceCompositionTetrahedronZeroFamily, ← Category.assoc, ← comp_whiskerRight,
    h, comp_whiskerRight, Category.assoc, spaceCompositionTetrahedron_pointed_face_one]

/-- 零面の中間作用は、元の同じ全三角形の中間作用そのもの。 -/
lemma spaceCompositionZeroFamily_middle_eq_original :
    simplexPrismVertex 2 1 A ≫ spaceCompositionTetrahedronZeroFamily s =
      simplexPrismVertex 2 1 A ≫ spaceSimplexPointedFamily s := by
  have h : prismEndpoint 0 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) =
      simplexPrismVertex 2 1 A := by
    apply SSet.hom_ext
    intro n
    rfl
  simpa only [← Category.assoc, h] using congrArg (fun t => prismEndpoint 0 A ≫ t)
    (spaceCompositionZeroFamily_last_eq_original s)

/-- 零面の終点作用も、元の同じ全三角形の終点作用そのもの。 -/
lemma spaceCompositionZeroFamily_target_eq_original :
    simplexPrismVertex 2 2 A ≫ spaceCompositionTetrahedronZeroFamily s =
      simplexPrismVertex 2 2 A ≫ spaceSimplexPointedFamily s := by
  have h : prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) =
      simplexPrismVertex 2 2 A := by
    apply SSet.hom_ext
    intro n
    rfl
  simpa only [← Category.assoc, h] using congrArg (fun t => prismEndpoint 1 A ≫ t)
    (spaceCompositionZeroFamily_last_eq_original s)

end SerrePositivity.InfinityCategories.F2
