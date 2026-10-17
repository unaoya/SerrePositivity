module

public import SerrePositivity.CategoryTheory.Simplex.PrefixInterval
public import SerrePositivity.CategoryTheory.Simplex.Naturality
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! # An extra degeneracy gives an actual map from the standard interval cylinder -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.ExtraDegeneracyInterval
variable {A : SimplicialObject.Augmented (Type v)}
  (ed : SimplicialObject.Augmented.ExtraDegeneracy A)

abbrev shifted : SSet.{v} := SimplexPrefix.functor.op ⋙ A.left

def extra : A.left ⟶ shifted (A := A) :=
  SimplexNaturality.ofFacesDegeneracies _ _ (fun n => ed.s n.unop.len)
    (by
      intro n i
      change A.left.δ i ≫ ed.s n = ed.s (n + 1) ≫
        A.left.map (SimplexPrefix.functor.map (SimplexCategory.δ i)).op
      rw [SimplexPrefix.map_δ]
      exact (ed.s_comp_δ n i).symm)
    (by
      intro n i
      change A.left.σ i ≫ ed.s (n + 1) = ed.s n ≫
        A.left.map (SimplexPrefix.functor.map (SimplexCategory.σ i)).op
      rw [SimplexPrefix.map_σ]
      exact (ed.s_comp_σ n i).symm)

def intervalMap : A.left ⊗ SimplexPrefix.interval ⟶ A.left where
  app n := ↾fun x => A.left.map (SimplexPrefix.cut n.unop x.2).op ((extra ed).app n x.1)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have hs := types_congr_hom ((extra ed).naturality θ) x.1
    change (extra ed).app m (A.left.map θ x.1) =
      A.left.map (SimplexPrefix.functor.map θ.unop).op ((extra ed).app n x.1) at hs
    change A.left.map (SimplexPrefix.cut m.unop (SimplexPrefix.interval.map θ x.2)).op
      ((extra ed).app m (A.left.map θ x.1)) =
        A.left.map θ (A.left.map (SimplexPrefix.cut n.unop x.2).op ((extra ed).app n x.1))
    rw [hs]
    have h := congrArg (fun f => A.left.map f.op) (SimplexPrefix.cut_naturality θ.unop x.2)
    simp only [op_comp, A.left.map_comp] at h
    exact (types_congr_hom h ((extra ed).app n x.1)).symm

end SerrePositivity.SimplicialModel.ExtraDegeneracyInterval
