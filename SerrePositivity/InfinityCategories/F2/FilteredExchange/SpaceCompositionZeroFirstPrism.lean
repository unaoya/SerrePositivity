module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroFirstCoslice
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionTetrahedronZeroFamily
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionMaximalizationFirstEdge
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedFamilyFaces
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroPointedHomotopy
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceTrianglePointedFirstEdgeEquality

/-!
概要：零面の実初辺を、元の最初の辺と最大化側の標準族の同じ実初辺へ揃える。
方針：同じ coslice 射へ全反転 Hom 係数を作用させ、最大化の辺の等式を使う。
規約：全係数と実 prism を保持。使われ方：零面の指定比較の実中間像を固定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))

/-- 零面の実初辺は、元の最初の辺の同じ全係数を持つ実 pointed 族。 -/
lemma spaceCompositionZeroFamily_first_eq_edge :
    (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ spaceCompositionTetrahedronZeroFamily s =
      spaceSimplexPointedFamily (SpaceInfinity.δ 2 s) := by
  let E := coherentCosliceSourcePrecomposition pointKanObject K ≫ pointedCoherentCosliceIso.hom
  let T := coherentCompositionTetrahedron s
  have hδ := SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ (0 : Fin 4))
    (spaceSimplexSourceCone T)
  have hz : spaceCompositionTetrahedronZeroFamily s =
      ((stdSimplex.δ (0 : Fin 4) ≫ SSet.yonedaEquiv.symm (spaceSimplexSourceCone T)) ▷ A) ≫
        E := (spaceCompositionZeroFamily_eq_coslice s).trans
      (congrArg (fun q => (q ▷ A) ≫ E) hδ.symm)
  calc
    _ = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫
        (((stdSimplex.δ (0 : Fin 4) ≫ SSet.yonedaEquiv.symm (spaceSimplexSourceCone T)) ▷ A) ≫
          E) := congrArg (fun q => (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ q) hz
    _ = (((stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4)) ≫
        SSet.yonedaEquiv.symm (spaceSimplexSourceCone T)) ▷ A) ≫ E := by
      simp only [comp_whiskerRight, Category.assoc]
    _ = (SSet.yonedaEquiv.symm (spaceSimplexSourceCone (SpaceInfinity.δ 2 s)) ▷ A) ≫ E :=
      congrArg (fun q => (q ▷ A) ≫ E) (spaceCompositionZeroFirstCoslice_map s)
    _ = _ := rfl

/-- 零面と元の全三角形の実初辺は、全係数上で厳密に一致する。 -/
lemma spaceCompositionZeroFamily_first_eq_original :
    (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ spaceCompositionTetrahedronZeroFamily s =
      (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ spaceSimplexPointedFamily s :=
  (spaceCompositionZeroFamily_first_eq_edge s).trans
    (spaceSimplexPointedFamily_positive_face s (1 : Fin 2)).symm

/-- 零面と最大化側の標準全族の実初辺も、同じ全係数上で厳密に一致する。 -/
lemma spaceCompositionZeroFamily_first_eq_standard :
    (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ spaceCompositionTetrahedronZeroFamily s =
      (stdSimplex.δ (2 : Fin 3) ▷ A) ≫
        spaceSimplexPointedFamily (coherentSimplexMaximalization s) := by
  exact (spaceCompositionZeroFamily_first_eq_original s).trans
    (eq_of_heq (spaceTrianglePointedFamily_first_heq_of_edge_eq
      (coherentSimplexMaximalization s) s (coherentCompositionMaximalization_first_edge s))).symm

end SerrePositivity.InfinityCategories.F2
