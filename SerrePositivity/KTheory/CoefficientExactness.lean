module
public import SerrePositivity.KTheory.CoefficientExtension
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Right exactness of coefficient extension of abelian groups -/
@[expose] public noncomputable section
universe v
namespace SerrePositivity
variable (E : Type v) [CommRing E]

/-- Tensoring a right exact sequence preserves its kernel–range equality.
The coefficient ring need not be flat over the integers. -/
lemma g0CoefficientMap_ker_eq_range {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (hfg : g.ker = f.range) (hg : Function.Surjective g) :
    (g0CoefficientMap E g).ker = (g0CoefficientMap E f).range := by
  have he : Function.Exact f.toIntLinearMap g.toIntLinearMap := by
    intro x
    exact Iff.of_eq (congrArg (fun H : AddSubgroup B => x ∈ H) hfg)
  exact LinearMap.exact_iff.mp (lTensor_exact E he hg)

end SerrePositivity
