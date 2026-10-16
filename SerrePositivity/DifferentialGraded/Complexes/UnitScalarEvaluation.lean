module
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation

/-! # 複体の射と整数単位スカラー -/
@[expose] public section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A]

lemma chain_units_smul {X Y : Complex A} (f : X ⟶ Y) (n : ℤ) (a : ℤˣ) (x : X.X n) :
    f.f n (a • x) = a • f.f n x := by
  simp only [Units.smul_def, map_zsmul]

end SerrePositivity.DifferentialGraded
