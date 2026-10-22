module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor

/-!
概要：元の代数射の準同型性に沿って connective 性を双方向に移す。
方針：各次数の exactAt の同値を元の複体の上界へ渡す。
規約：全代数の準同型反転は仮定しない。使われ方：混合 class 模型の値への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)

lemma quasiIso_isConnective_iff (hf : QuasiIso f.hom) :
    IsConnective R A ↔ IsConnective R B := by
  have := hf
  constructor
  · intro hA
    have : A.X.IsLE 0 := hA
    apply (CochainComplex.isLE_iff _ 0).2
    intro i hi
    exact (exactAt_iff_of_quasiIsoAt f.hom i).1
      (CochainComplex.exactAt_of_isLE A.X 0 i hi)
  · intro hB
    have : B.X.IsLE 0 := hB
    apply (CochainComplex.isLE_iff _ 0).2
    intro i hi
    exact (exactAt_iff_of_quasiIsoAt f.hom i).2
      (CochainComplex.exactAt_of_isLE B.X 0 i hi)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
