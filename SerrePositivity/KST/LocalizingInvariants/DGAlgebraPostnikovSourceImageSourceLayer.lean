module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageModelMap

/-!
概要：元の源上段から源側像拡大への実射は、層の同型の下で元の像射影になる。
方針：係数射影に沿う層同型の自然性を、元の準同型比較との厳密な合成式へ移す。
規約：上段の比較同型を明示。使われ方：実因子分解の源射の新しい層での全射性。
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

lemma postnikovSourceImageModelMap_layer :
    homologyMap (postnikovSourceImageModelMap R f n hn).hom (-(n + 1)) ≫
      (postnikovSourceImageLayerHomologyIso R f n hn).hom =
        (postnikovClassModelLayerHomologyIso R B n hn).hom ≫
          factorThruImage (homologyMap f.hom (-(n + 1))) := by
  let N := postnikovShiftedLayerBimodule R B n hn 1
  let I := postnikovShiftedLayerImage R f n hn 1
  let a := postnikovPerturbedClass R B n hn
  let a' := postnikovSourceImageClass R f n hn
  let j : ℤ := -(n + 1)
  have h₀ := postnikovPerturbedSource_homology_zero R (B := B) n hn (j - 1) (by dsimp [j]; omega)
  have h₁ := postnikovPerturbedSource_homology_zero R (B := B) n hn j (by dsimp [j]; omega)
  have hm : homologyMap (postnikovSourceImageModelMap R f n hn).hom j ≫
      (SquareZeroExtension.layerHomologyIso I a' j h₀ h₁).hom =
        (SquareZeroExtension.layerHomologyIso N a j h₀ h₁).hom ≫
          homologyMap (postnikovShiftedLayerImageProjection R f n hn 1).hom (j - 1) :=
    SquareZeroExtension.layerHomologyIso_naturality N I a a' (𝟙 _) (𝟙 _)
      (postnikovSourceImageCoefficientMap R f n hn)
      (postnikovShiftedLayerImageProjection R f n hn 1).hom rfl
      (by simp [a', a, postnikovSourceImageClass]) j h₀ h₁ h₀ h₁
  change homologyMap (postnikovSourceImageModelMap R f n hn).hom j ≫
    (SquareZeroExtension.layerHomologyIso I a' j h₀ h₁).hom ≫
      (postnikovShiftedLayerImageHomologyIso R f n hn 1).hom =
        ((SquareZeroExtension.layerHomologyIso N a j h₀ h₁).hom ≫
          (postnikovShiftedLayerHomologyIso R B n hn 1).hom) ≫ _
  rw [← Category.assoc, hm, Category.assoc,
    postnikovShiftedLayerImageHomologyIso_projection, Category.assoc]

lemma postnikovSourceImageFactor_layer :
    homologyMap (postnikovSourceImageFactor R f n hn).hom (-(n + 1)) ≫
      (postnikovSourceImageLayerHomologyIso R f n hn).hom =
        (postnikovUpperClassLayerHomologyIso R B n hn).hom ≫
          factorThruImage (homologyMap f.hom (-(n + 1))) := by
  have he : (postnikovHomotopyPullbackComparison R B n hn).hom ≫
      (postnikovSourceImageModelMap R f n hn).hom = (postnikovSourceImageFactor R f n hn).hom :=
    congrArg Mon.Hom.hom (postnikovSourceImageModelMap_comparison R f n hn)
  change _ = (homologyMap (postnikovHomotopyPullbackComparison R B n hn).hom (-(n + 1)) ≫
    (postnikovClassModelLayerHomologyIso R B n hn).hom) ≫ _
  rw [← he, homologyMap_comp, Category.assoc, postnikovSourceImageModelMap_layer, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
