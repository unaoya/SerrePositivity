module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageHomologySquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageArrowFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageHomology
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionLayerNaturality

/-!
概要：源側像拡大の層同型は、元の代数の任意の可換正方形に自然である。
方針：実平方零 class の層自然性と、元の係数像のホモロジー同型の正方形を合成する。
規約：元の模型射と元のホモロジー像射を保持。使われ方：層比較の実自然同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)
  (f : B ⟶ C) (f' : B' ⟶ C') (s : B ⟶ B') (t : C ⟶ C') (h : f ≫ t = s ≫ f')

lemma postnikovSourceImageLayerHomologyIso_square :
    homologyMap (postnikovSourceImageExtensionSquareMap R n hn f f' s t h).hom (-(n + 1)) ≫
      (postnikovSourceImageLayerHomologyIso R f' n hn).hom =
        (postnikovSourceImageLayerHomologyIso R f n hn).hom ≫
          image.map (postnikovHomologySquare R n f f' s t h) := by
  let I := postnikovShiftedLayerImage R f n hn 1
  let I' := postnikovShiftedLayerImage R f' n hn 1
  let a := postnikovSourceImageClass R f n hn
  let a' := postnikovSourceImageClass R f' n hn
  let j : ℤ := -(n + 1)
  have h₀ := postnikovPerturbedSource_homology_zero R (B := B) n hn (j - 1) (by dsimp [j]; omega)
  have h₁ := postnikovPerturbedSource_homology_zero R (B := B) n hn j (by dsimp [j]; omega)
  have h₀' := postnikovPerturbedSource_homology_zero R (B := B') n hn (j - 1) (by dsimp [j]; omega)
  have h₁' := postnikovPerturbedSource_homology_zero R (B := B') n hn j (by dsimp [j]; omega)
  have hm : homologyMap (postnikovSourceImageExtensionSquareMap R n hn f f' s t h).hom j ≫
      (SquareZeroExtension.layerHomologyIso I' a' j h₀' h₁').hom =
        (SquareZeroExtension.layerHomologyIso I a j h₀ h₁).hom ≫
          homologyMap (postnikovShiftedLayerImageSquareMap R n hn 1 f f' s t h).hom (j - 1) :=
    SquareZeroExtension.layerHomologyIso_naturality I I' a a' (postnikovPerturbedMap R s n hn)
      (postnikovMap R s n) (postnikovSourceImageSquareZeroMap R n hn f f' s t h)
      (postnikovShiftedLayerImageSquareMap R n hn 1 f f' s t h).hom rfl
      (postnikovSourceImageClass_square R n hn f f' s t h) j h₀ h₁ h₀' h₁'
  change homologyMap (postnikovSourceImageExtensionSquareMap R n hn f f' s t h).hom j ≫
    (SquareZeroExtension.layerHomologyIso I' a' j h₀' h₁').hom ≫
      (postnikovShiftedLayerImageHomologyIso R f' n hn 1).hom =
        ((SquareZeroExtension.layerHomologyIso I a j h₀ h₁).hom ≫
          (postnikovShiftedLayerImageHomologyIso R f n hn 1).hom) ≫ _
  rw [← Category.assoc, hm, Category.assoc, postnikovShiftedLayerImageHomologyIso_square,
    Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
