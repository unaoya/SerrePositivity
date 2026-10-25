module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
/-!
概要：自由 sphere と任意複体の tensor を、同じ複体の整数 shift へ同定する。
方針：sphere を shift した単位複体と比較し、左 tensor shift と左単位を合成する。
規約：非有界複体・全整数次数を扱い、元の tensor を保つ。
使われ方：c′ のシフト自由加群間閉射から元の Hom の斉次係数を取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R]

def complexSphereUnitShiftIso (n : ℤ) : complexSphere R n ≅ (𝟙_ (Complex R))⟦-n⟧ :=
  (((CochainComplex.singleFunctors (ModuleCat.{u} R)).shiftIso (-n) n 0 (by omega)).app
    (𝟙_ (ModuleCat R))).symm

def complexSphereTensorShiftIso (n : ℤ) (K : Complex R) :
    complexSphere R n ⊗ K ≅ K⟦-n⟧ :=
  (tensorIso (complexSphereUnitShiftIso R n) (Iso.refl K)) ≪≫
    SerrePositivity.cochainTensorShiftLeft (𝟙_ (Complex R)) K (-n) ≪≫
    (shiftFunctor (Complex R) (-n)).mapIso (λ_ K)

end SerrePositivity.DifferentialGraded
