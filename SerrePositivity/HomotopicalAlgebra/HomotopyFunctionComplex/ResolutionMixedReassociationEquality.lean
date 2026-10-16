module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterComposition

/-! # Reassociation is equality transport of the same entire indexing functor -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedReassociation

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociationEquality
variable (C : Type u) [Category.{v} C] [ModelCategory C]

lemma finalLeft_eq : finalLeft C = cornerD C :=
  Functor.ext_of_iso (toFinal C) (assocEq C) (fun _ => rfl)

lemma toFinal_eq : toFinal C = eqToIso (finalLeft_eq C) := by
  apply Iso.ext
  apply NatTrans.ext
  funext p
  exact (eqToHom_app (finalLeft_eq C) p).symm

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociationEquality
