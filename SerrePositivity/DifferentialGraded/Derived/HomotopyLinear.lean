module
public import SerrePositivity.DifferentialGraded.Derived.Linear

/-! # K(D)から主導来圏への比較のA線形性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K(D)から主導来圏への関手はA線形。Qとの比較と商関手の充満・本質的全射性から降下する。 -/
instance moduleHomotopyToDerivedClosedLinear : (moduleHomotopyToDerivedClosed A D).Linear A := by
  have : (moduleToHomotopy A D ⋙ moduleHomotopyToDerivedClosed A D).Linear A :=
    Functor.linear_of_iso A (moduleToHomotopyDerivedIso A D).symm
  exact Functor.linear_of_full_essSurj_comp (moduleToHomotopy A D) _

end SerrePositivity.DifferentialGraded
