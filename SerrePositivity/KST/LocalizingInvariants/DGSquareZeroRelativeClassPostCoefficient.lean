module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassComposition

/-!
概要：元の class 模型射の後に係数模型射を合成し、元の class 経路の係数像で表示する。
方針：係数模型射を定数経路付き class 模型射として、既存の厳密合成則を使う。
規約：元の両脚と class 経路の全射を保持。使われ方：fixed roof の右模型合成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N P : Bimod A A}
  (m : M ⟶ N) (n : N ⟶ P)
  (a : W ⟶ SquareZero.algebra A M) (b : W ⟶ SquareZero.algebra A N) {q : W ⟶ A}
  (v : SquareZero.RelativeWitness q N (a ≫ SquareZero.coefficientMap A m) b)

def postCoefficientReflexivity := SquareZero.RelativeWitness.refl
  (b ≫ SquareZero.coefficientMap A n) (v.mapCoefficient n).target_projection

def postCoefficientClassWitness := composeClassWitness m n a b
  (b ≫ SquareZero.coefficientMap A n) v (postCoefficientReflexivity m n a b v)

lemma postCoefficientClassWitness_hom : (postCoefficientClassWitness m n a b v).hom =
    v.hom ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A n) := by
  apply Mon.Hom.ext
  rw [postCoefficientClassWitness, composeClassWitness_hom_linear]
  change (v.hom ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A n)).hom -
    ((b ≫ SquareZero.coefficientMap A n) ≫
      DGAlgebra.Path.diagonal R (SquareZero.algebra A P)).hom +
    ((b ≫ SquareZero.coefficientMap A n) ≫
      DGAlgebra.Path.diagonal R (SquareZero.algebra A P)).hom = _
  abel

lemma postCoefficientClassWitness_post {Y : Mon (Complex R)}
    (k : SquareZero.algebra A P ⟶ Y) :
    (postCoefficientClassWitness m n a b v).hom ≫ DGAlgebra.Path.map R k =
      v.hom ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A n ≫ k) := by
  rw [postCoefficientClassWitness_hom, Category.assoc, ← DGAlgebra.Path.map_comp]

lemma classModelMap_postCoefficient : classModelMap m a b v ≫
    coefficientModelMap n b (b ≫ SquareZero.coefficientMap A n) rfl =
    classModelMap (m ≫ n) a (b ≫ SquareZero.coefficientMap A n)
      (postCoefficientClassWitness m n a b v) := by
  let w := postCoefficientReflexivity m n a b v
  let h := classModelMap_eq_coefficient n b (b ≫ SquareZero.coefficientMap A n) w rfl rfl
  let k := classModelMap_comp m n a b (b ≫ SquareZero.coefficientMap A n) v w
  exact (congrArg (fun t => classModelMap m a b v ≫ t) h.symm).trans k

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
