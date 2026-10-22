module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFunctor

/-!
概要：実係数射は、同じ底の相対 class 経路を元の底のまま移す。
方針：元の経路を係数代数射で後合成し、底への射影の厳密な式を使う。
規約：係数射の準同型性は要求しない。使われ方：Γ と class 経路の合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N : Bimod A A}

lemma coefficientMap_id (A : Mon (Complex R)) (M : Bimod A A) :
    coefficientMap A (𝟙 M) = 𝟙 (algebra A M) := (coefficientFunctor A).map_id M

lemma zeroSection_coefficientMap (m : M ⟶ N) : zeroSection A M ≫ coefficientMap A m =
    zeroSection A N := by
  apply Mon.Hom.ext
  change biprod.inl ≫ biprod.map (𝟙 A.X) m.hom = biprod.inl
  rw [biprod.inl_map, Category.id_comp]

namespace RelativeWitness
variable {q : W ⟶ A} {a b : W ⟶ algebra A M}

def mapCoefficient (v : RelativeWitness q M a b) (m : M ⟶ N) :
    RelativeWitness q N (a ≫ coefficientMap A m) (b ≫ coefficientMap A m) where
  toWitness := v.toWitness.postcomp (coefficientMap A m)
  projection_eq := by
    change (v.hom ≫ DGAlgebra.Path.map R (coefficientMap A m)) ≫
      DGAlgebra.Path.map R (projection A N) = _
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, coefficientMap_projection, v.projection_eq]

lemma mapCoefficient_hom (v : RelativeWitness q M a b) (m : M ⟶ N) :
    (v.mapCoefficient m).hom = v.hom ≫ DGAlgebra.Path.map R (coefficientMap A m) := rfl

end RelativeWitness
end SerrePositivity.KST.LocalizingInvariants.SquareZero
