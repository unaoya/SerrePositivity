module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.FactorZeroTransport
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-! C 因子から D 因子への全 Hom の、二つの対角成分の通常ホモトピー零性。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R]
local notation "Qh" => _root_.HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

lemma dgGluingComplexHomotopyZero_of_factorZero (P : Complex R)
    (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R (Complex R) P) : IsZero ((Qh).obj P) :=
  (complexHomotopyComparison R).map_isZero hP

lemma dgGluingComplexBiproduct_homotopyZero (P Q : Complex R)
    (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R (Complex R) P)
    (hQ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R (Complex R) Q) : IsZero ((Qh).obj (P ⊞ Q)) := by
  let := preservesBinaryBiproduct_of_preservesBinaryProduct (Qh) (X := P) (Y := Q)
  exact ((biprod_isZero_iff _ _).2
    ⟨dgGluingComplexHomotopyZero_of_factorZero R P hP,
      dgGluingComplexHomotopyZero_of_factorZero R Q hQ⟩).of_iso ((Qh).mapBiprod P Q)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
