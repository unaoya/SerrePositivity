module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassLayerHomology

/-!
概要：源側像拡大から元の標的模型への実射は、層同型の下で元の像包含になる。
方針：実 class 正方形の層の自然性と、係数像の包含を保つホモロジー比較を合成する。
規約：元の係数包含と実模型射を使用。使われ方：実因子分解の標的射の単射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovSourceImageToTarget_layer :
    homologyMap (postnikovSourceImageToTarget R f n hn).hom (-(n + 1)) ≫
      (postnikovClassModelLayerHomologyIso R C n hn).hom =
        (postnikovSourceImageLayerHomologyIso R f n hn).hom ≫
          image.ι (homologyMap f.hom (-(n + 1))) := by
  let I := postnikovShiftedLayerImage R f n hn 1
  let N := postnikovShiftedLayerBimodule R C n hn 1
  let a := postnikovSourceImageClass R f n hn
  let a' := postnikovPerturbedClass R C n hn
  let j : ℤ := -(n + 1)
  have h₀ := postnikovPerturbedSource_homology_zero R (B := B) n hn (j - 1) (by dsimp [j]; omega)
  have h₁ := postnikovPerturbedSource_homology_zero R (B := B) n hn j (by dsimp [j]; omega)
  have h₀' := postnikovPerturbedSource_homology_zero R (B := C) n hn (j - 1) (by dsimp [j]; omega)
  have h₁' := postnikovPerturbedSource_homology_zero R (B := C) n hn j (by dsimp [j]; omega)
  have hm : homologyMap (postnikovSourceImageToTarget R f n hn).hom j ≫
      (SquareZeroExtension.layerHomologyIso N a' j h₀' h₁').hom =
        (SquareZeroExtension.layerHomologyIso I a j h₀ h₁).hom ≫
          homologyMap (postnikovShiftedLayerImageInclusion R f n hn 1).hom (j - 1) :=
    SquareZeroExtension.layerHomologyIso_naturality I N a a'
      (postnikovPerturbedMap R f n hn) (postnikovMap R f n)
      (postnikovImageClassTargetMap R f n hn)
      (postnikovShiftedLayerImageInclusion R f n hn 1).hom rfl
      (postnikovSourceImageClass_inclusion R f n hn).symm j h₀ h₁ h₀' h₁'
  change homologyMap (postnikovSourceImageToTarget R f n hn).hom j ≫
    (SquareZeroExtension.layerHomologyIso N a' j h₀' h₁').hom ≫
      (postnikovShiftedLayerHomologyIso R C n hn 1).hom =
        ((SquareZeroExtension.layerHomologyIso I a j h₀ h₁).hom ≫
          (postnikovShiftedLayerImageHomologyIso R f n hn 1).hom) ≫ _
  rw [← Category.assoc, hm, Category.assoc,
    ← postnikovShiftedLayerImageHomologyIso_inclusion, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
