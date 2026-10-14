module

public import SerrePositivity.KTheory.Adams.KoszulSquareModel

/-! # The signed exchange on the four standard Koszul tensor generators -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
variable {R : Type u} [CommRing R]

namespace Adams

abbrev scalarTensorDiagonal : ModuleCat.of R R ⟶ ModuleCat.of R R ⊗ ModuleCat.of R R :=
  (λ_ (ModuleCat.of R R)).inv

lemma scalarTensorDiagonal_braiding :
    scalarTensorDiagonal (R := R) ≫
      (β_ (ModuleCat.of R R) (ModuleCat.of R R)).hom = scalarTensorDiagonal := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change r ⊗ₜ[R] (1 : R) = (1 : R) ⊗ₜ[R] r
  simpa only [smul_eq_mul, mul_one] using
    (TensorProduct.smul_tmul (R := R) r (1 : R) (1 : R))

lemma scalarTensorDiagonal_tensor_braiding {A B : ModuleCat.{u} R}
    (f : ModuleCat.of R R ⟶ A) (g : ModuleCat.of R R ⟶ B) :
    scalarTensorDiagonal ≫ (f ⊗ₘ g) ≫ (β_ A B).hom =
      scalarTensorDiagonal ≫ (g ⊗ₘ f) := by
  rw [BraidedCategory.braiding_naturality, ← Category.assoc, scalarTensorDiagonal_braiding]

def oneKoszulTensorGenerator (a : R) (i j n : ℤ) (h : i + j = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j) :
    ModuleCat.of R R ⟶ (tensorSquare (oneKoszulComplex a)).X n :=
  scalarTensorDiagonal ≫ (f ⊗ₘ g) ≫ ιTensorObj (oneKoszulComplex a) (oneKoszulComplex a) i j n h

lemma oneKoszulTensorGenerator_swap (a : R) (i j n : ℤ) (h : i + j = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j) :
    oneKoszulTensorGenerator a i j n h f g ≫ (tensorSquareSwap (oneKoszulComplex a)).f n =
      (i * j).negOnePow • oneKoszulTensorGenerator a j i n (by omega) g f := by
  dsimp [oneKoszulTensorGenerator]
  simp only [Category.assoc]
  rw [ιTensorObj_tensorSquareSwap]
  rw [Linear.comp_units_smul, Linear.comp_units_smul]
  congr 1
  rw [← Category.assoc (f ⊗ₘ g), ← Category.assoc,
    scalarTensorDiagonal_tensor_braiding]
  exact Category.assoc _ _ _

abbrev oneKoszulSquareBottom (a : R) :=
  oneKoszulTensorGenerator a 0 0 0 rfl (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv

abbrev oneKoszulSquareLeft (a : R) :=
  oneKoszulTensorGenerator a (-1) 0 (-1) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv

abbrev oneKoszulSquareRight (a : R) :=
  oneKoszulTensorGenerator a 0 (-1) (-1) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv

abbrev oneKoszulSquareTop (a : R) :=
  oneKoszulTensorGenerator a (-1) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulSquareBottom_swap (a : R) :
    oneKoszulSquareBottom a ≫ (tensorSquareSwap (oneKoszulComplex a)).f 0 =
      oneKoszulSquareBottom a := by
  simpa using oneKoszulTensorGenerator_swap a 0 0 0 rfl
    (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv

lemma oneKoszulSquareLeft_swap (a : R) :
    oneKoszulSquareLeft a ≫ (tensorSquareSwap (oneKoszulComplex a)).f (-1) =
      oneKoszulSquareRight a := by
  simpa using oneKoszulTensorGenerator_swap a (-1) 0 (-1) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv

lemma oneKoszulSquareRight_swap (a : R) :
    oneKoszulSquareRight a ≫ (tensorSquareSwap (oneKoszulComplex a)).f (-1) =
      oneKoszulSquareLeft a := by
  simpa using oneKoszulTensorGenerator_swap a 0 (-1) (-1) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulSquareTop_swap (a : R) :
    oneKoszulSquareTop a ≫ (tensorSquareSwap (oneKoszulComplex a)).f (-2) =
      -oneKoszulSquareTop a := by
  simpa using oneKoszulTensorGenerator_swap a (-1) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulSquarePositive_swap (a : R) :
    (oneKoszulSquareLeft a + oneKoszulSquareRight a) ≫
      (tensorSquareSwap (oneKoszulComplex a)).f (-1) =
    oneKoszulSquareLeft a + oneKoszulSquareRight a := by
  rw [Preadditive.add_comp, oneKoszulSquareLeft_swap, oneKoszulSquareRight_swap, add_comm]

lemma oneKoszulSquareNegative_swap (a : R) :
    (oneKoszulSquareLeft a - oneKoszulSquareRight a) ≫
      (tensorSquareSwap (oneKoszulComplex a)).f (-1) =
    -(oneKoszulSquareLeft a - oneKoszulSquareRight a) := by
  rw [Preadditive.sub_comp, oneKoszulSquareLeft_swap, oneKoszulSquareRight_swap, neg_sub]

end Adams
end SerrePositivity
