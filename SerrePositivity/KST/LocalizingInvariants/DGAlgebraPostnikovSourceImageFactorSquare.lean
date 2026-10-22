module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageExtensionSquareLaws
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageFactorisation

/-!
概要：元の源上段から源側像拡大への実射は、元の代数の正方形に自然である。
方針：二脚と定数乗法的経路の三成分を計算し、元の摂動包含・class の自然性を使う。
規約：元の source factor の射を保持。使われ方：連結な源比較の実自然変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)
  (f : B ⟶ C) (f' : B' ⟶ C') (s : B ⟶ B') (t : C ⟶ C') (h : f ≫ t = s ≫ f')

lemma postnikovSourceImageFactor_square : postnikovMap R s (n + 1) ≫
    postnikovSourceImageFactor R f' n hn =
      postnikovSourceImageFactor R f n hn ≫
        postnikovSourceImageExtensionSquareMap R n hn f f' s t h := by
  apply HomotopyPullbackModel.hom_ext R (postnikovSourceImageClass R f' n hn)
    (SquareZero.zeroSection (postnikov R B' n) (postnikovShiftedLayerImage R f' n hn 1))
  · rw [Category.assoc, postnikovSourceImageFactor_left, Category.assoc,
      postnikovSourceImageExtensionSquareMap_left, ← Category.assoc,
      postnikovSourceImageFactor_left]
    exact (postnikovPerturbedInclusion_naturality R s n hn).symm
  · rw [Category.assoc, postnikovSourceImageFactor_right, Category.assoc,
      postnikovSourceImageExtensionSquareMap_right, ← Category.assoc,
      postnikovSourceImageFactor_right]
    exact postnikovTransition_naturality R B s (n + 1) n (by omega)
  · rw [Category.assoc, postnikovSourceImageFactor_path, Category.assoc,
      postnikovSourceImageExtensionSquareMap_path,
      ← Category.assoc (postnikovSourceImageFactor R f n hn), postnikovSourceImageFactor_path]
    simp only [Category.assoc, Path.diagonal_naturality]
    rw [← Category.assoc (postnikovMap R s (n + 1)),
      ← postnikovPerturbedInclusion_naturality, Category.assoc,
      ← Category.assoc (postnikovPerturbedMap R s n hn),
      postnikovSourceImageClass_square R n hn f f' s t h,
      Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
