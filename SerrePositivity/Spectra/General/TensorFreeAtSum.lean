module

public import SerrePositivity.Spectra.General.TensorClosed
public import SerrePositivity.Spectra.SymmetricSequence.FreePairConvolution
public import SerrePositivity.CategoryTheory.Monoidal.Mod.FreeTensor

/-! # Tensor products of general free spectra are free in the sum degree

This is the actual balanced tensor over Sym(K), with naturality in both
coefficient objects. The calculation does not use any model structure.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

def tensorFreePair (X Y : SymmetricSequence C) :
    freeObj K X ⊗ freeObj K Y ≅ freeObj K (X ⊗ Y) :=
  MonoidalBalancedTensor.freePairIso (SymmetricSequence.tensorPowerSequence K) X Y

def tensorFreeAtSum (m n : ℕ) (X Y : C) :
    (freeAt (K := K) m).obj X ⊗ (freeAt (K := K) n).obj Y ≅
      (freeAt (K := K) (m + n)).obj (X ⊗ Y) :=
  tensorFreePair ((SymmetricSequence.freeAt m).obj X) ((SymmetricSequence.freeAt n).obj Y) ≪≫
    (freeFunctor K).mapIso (SymmetricSequence.freePairConvolutionIso m n X Y)

lemma tensorFreeAtSum_naturality (m n : ℕ) {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((freeAt (K := K) m).map f ⊗ₘ (freeAt (K := K) n).map g) ≫
        (tensorFreeAtSum m n X' Y').hom =
      (tensorFreeAtSum (K := K) m n X Y).hom ≫ (freeAt (K := K) (m + n)).map (f ⊗ₘ g) := by
  change _ ≫ (tensorFreePair _ _).hom ≫
      (freeFunctor K).map (SymmetricSequence.freePairConvolutionIso m n X' Y').hom =
    ((tensorFreePair _ _).hom ≫
      (freeFunctor K).map (SymmetricSequence.freePairConvolutionIso m n X Y).hom) ≫
        (freeFunctor K).map ((SymmetricSequence.freeAt (m + n)).map (f ⊗ₘ g))
  simp only [freeAt, Functor.comp_map]
  have hpair :
      ((freeFunctor K).map ((SymmetricSequence.freeAt m).map f) ⊗ₘ
        (freeFunctor K).map ((SymmetricSequence.freeAt n).map g)) ≫
          (tensorFreePair _ _).hom =
        (tensorFreePair (K := K) _ _).hom ≫
          (freeFunctor K).map
            ((SymmetricSequence.freeAt m).map f ⊗ₘ (SymmetricSequence.freeAt n).map g) :=
    MonoidalBalancedTensor.freePair_naturality (SymmetricSequence.tensorPowerSequence K)
      ((SymmetricSequence.freeAt m).map f) ((SymmetricSequence.freeAt n).map g)
  rw [← Category.assoc, hpair, Category.assoc,
    ← Functor.map_comp, SymmetricSequence.freePairConvolutionIso_naturality,
    Functor.map_comp, Category.assoc]

/-- Tensor two spectra free in the indicated degrees. -/
def tensorFreeAtBifunctor (m n : ℕ) : C × C ⥤ GeneralSymmetricSpectrum C K :=
  (freeAt (K := K) m).prod (freeAt (K := K) n) ⋙
    MonoidalBalancedTensor.moduleBifunctor (SymmetricSequence.tensorPowerSequence K)

/-- Tensor the coefficients and take the spectrum free in the sum degree. -/
def freeAtTensorBifunctor (m n : ℕ) : C × C ⥤ GeneralSymmetricSpectrum C K :=
  CategoryTheory.MonoidalCategory.tensor C ⋙ freeAt (K := K) (m + n)

/-- The free tensor comparison is natural in the two coefficient objects. -/
def tensorFreeAtSumNatIso (m n : ℕ) :
    tensorFreeAtBifunctor (K := K) m n ≅ freeAtTensorBifunctor m n :=
  NatIso.ofComponents (fun XY => tensorFreeAtSum (K := K) m n XY.1 XY.2)
    (fun fg => tensorFreeAtSum_naturality m n fg.1 fg.2)

end SerrePositivity.GeneralSymmetricSpectrum
