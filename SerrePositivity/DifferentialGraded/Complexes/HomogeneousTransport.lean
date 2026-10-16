module
public import SerrePositivity.DifferentialGraded.Complexes.ShiftCoherence

/-! # 斉次写像の始域次数の逆輸送 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma homogeneous_XIsoOfEq_inv_comp {P Q : Complex A} {p i i' j : ℤ}
    (f : Homogeneous P Q p) (hi : i = i') (hij : i + p = j) :
    (P.XIsoOfEq hi).inv ≫ f.v i j hij = f.v i' j (by omega) := by
  subst i'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.id_comp]

end SerrePositivity.DifferentialGraded
