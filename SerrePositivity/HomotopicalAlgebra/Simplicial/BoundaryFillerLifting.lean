module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterExtension

/-! # All-monomorphism lifting from boundary fillers without any model structure -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.BoundaryFillerLifting
variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P)
  {A K : SSet.{v}} (j : A ⟶ K) [Mono j]

def rule : SkeletalCellGluing.Rule (Q := P) j := by
  intro n a c
  let ex := hp n (SkeletalCellGluing.boundary j c ≫ a)
  exact ⟨ex.choose, ex.choose_spec⟩

def extend (a : A ⟶ P) : K ⟶ P := SkeletalCellGluing.assemble j (rule hp j) a

@[reassoc]
lemma extend_initial (a : A ⟶ P) : j ≫ extend hp j a = a :=
  SkeletalCellGluing.assemble_initial _ _ _

include hp in
lemma terminal_rightLifting : (MorphismProperty.monomorphisms SSet.{v}).rlp
    (SSet.stdSimplex.isTerminalObj₀.from P) := by
  intro A K j hj
  have : Mono j := hj
  constructor
  intro a _b sq
  exact CommSq.HasLift.mk'
    { l := extend hp j a
      fac_left := extend_initial hp j a
      fac_right := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ }

end SerrePositivity.SimplicialModel.BoundaryFillerLifting
