module

public import SerrePositivity.HomotopicalAlgebra.Topological.BasedContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WeakEquivalence
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-! # Geometric weak equivalences between the actual standard simplices

The realization of a standard simplex is the actual topological standard
simplex. Linear contraction to any basepoint fixes that basepoint, so it
contracts every cubical loop relative to the entire boundary.
-/

@[expose] public section
universe u v
noncomputable section
open CategoryTheory Convexity
open SerrePositivity.TopologicalHomotopy

namespace SerrePositivity.SimplicialHomotopy

lemma continuous_simplexContraction {M : Type v} [Finite M] (x : StdSimplex ℝ M) :
    Continuous (fun z : unitInterval × StdSimplex ℝ M ↦
      convexCombPair (R := ℝ) (unitInterval.symm z.1) z.1
        (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) z.2 x) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ M).continuous_iff]
  unfold Function.comp
  apply continuous_pi
  intro i
  simp only [unitInterval.coe_symm_eq, StdSimplex.weights_convexCombPair, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

def simplexBasedContraction {M : Type v} [Finite M] (x : StdSimplex ℝ M) :
    BasedContraction x where
  toHomotopy :=
    { toFun z := convexCombPair (R := ℝ) (unitInterval.symm z.1) z.1
        (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) z.2 x
      continuous_toFun := continuous_simplexContraction x
      map_zero_left _ := by simp
      map_one_left _ := by simp }
  prop' t z hz := by
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    subst z
    simp

def topSimplexBasedContraction (n : SimplexCategory) (x : SimplexCategory.toTop.{u}.obj n) :
    BasedContraction x :=
  BasedContraction.ofHomeomorph Homeomorph.ulift x (simplexBasedContraction x.down)

def realizedSimplexBasedContraction (n : SimplexCategory)
    (x : SSet.toTop.obj (SSet.stdSimplex.{u}.obj n)) : BasedContraction x :=
  BasedContraction.ofHomeomorph (TopCat.homeoOfIso (SSet.toTopSimplex.app n)) x
    (topSimplexBasedContraction n _)

lemma stdSimplex_map_weakEquivalence {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences (SSet.stdSimplex.{u}.map f) := by
  have (k : SimplexCategory) : PathConnectedSpace (SSet.toTop.obj (SSet.stdSimplex.{u}.obj k)) :=
    (TopCat.homeoOfIso (SSet.toTopSimplex.app k)).symm.pathConnectedSpace
  exact weakHomotopyEquivalences_of_basedContractions
    (fun x ↦ ⟨realizedSimplexBasedContraction n x⟩)
    (fun x ↦ ⟨realizedSimplexBasedContraction m x⟩) (SSet.toTop.map (SSet.stdSimplex.map f))

end SerrePositivity.SimplicialHomotopy
