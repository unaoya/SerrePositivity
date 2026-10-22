module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageExtension

/-!
概要：源の像拡大による二射の合成が、元の上段の射を厳密に回収する。
方針：摂動包含の自然性と定数経路の自然性を、実模型の三成分の一意性へ渡す。
規約：終域は元の標的上段から準同型比較される実模型。使われ方：LT のレベル因子分解。
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

lemma postnikovPerturbedInclusion_naturality : postnikovPerturbedInclusion R B n hn ≫
    postnikovPerturbedMap R f n hn =
      postnikovMap R f (n + 1) ≫ postnikovPerturbedInclusion R C n hn := by
  apply Mon.Hom.ext
  apply HomologicalComplex.hom_ext
  intro j
  change (postnikovPerturbedInclusion R B n hn).hom.f j ≫
    (postnikovPerturbedMap R f n hn).hom.f j =
      (postnikovMap R f (n + 1)).hom.f j ≫ (postnikovPerturbedInclusion R C n hn).hom.f j
  rw [postnikovPerturbedMap_f]
  exact congrArg (fun t => t.f j)
    (biprod.inl_map (postnikovMap R f (n + 1)).hom ((postnikovLayerMap R f n)⟦(1 : ℤ)⟧'))

lemma postnikovHomotopyPullbackComparison_path (D : Mon (Complex R)) [D.X.IsStrictlyLE 0] :
    postnikovHomotopyPullbackComparison R D n hn ≫ HomotopyPullbackModel.path R _ _ =
      postnikovPerturbedInclusion R D n hn ≫ postnikovPerturbedClass R D n hn ≫
        Path.diagonal R _ := by
  rw [postnikovHomotopyPullbackComparison, Category.assoc,
    HomotopyPullbackModel.comparison_path, ← Category.assoc, postnikovStrictPullbackIso_fst]

lemma postnikovSourceImageFactorisation : postnikovSourceImageFactor R f n hn ≫
    postnikovSourceImageToTarget R f n hn =
      postnikovMap R f (n + 1) ≫ postnikovHomotopyPullbackComparison R C n hn := by
  apply HomotopyPullbackModel.hom_ext R (postnikovPerturbedClass R C n hn)
    (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1))
  · rw [Category.assoc, postnikovSourceImageToTarget_left, ← Category.assoc,
      postnikovSourceImageFactor_left, Category.assoc, postnikovHomotopyPullbackComparison_left,
      postnikovPerturbedInclusion_naturality]
  · rw [Category.assoc, postnikovSourceImageToTarget_right, ← Category.assoc,
      postnikovSourceImageFactor_right, Category.assoc, postnikovHomotopyPullbackComparison_right]
    exact (postnikovTransition_naturality R B f (n + 1) n (by omega)).symm
  · rw [Category.assoc, postnikovSourceImageToTarget_path, ← Category.assoc,
      postnikovSourceImageFactor_path, Category.assoc, Category.assoc,
      Path.diagonal_naturality, ← Category.assoc (postnikovSourceImageClass R f n hn),
      postnikovSourceImageClass_inclusion, ← Category.assoc (postnikovPerturbedInclusion R B n hn),
      ← Category.assoc, postnikovPerturbedInclusion_naturality]
    simpa only [Category.assoc] using (congrArg
      (fun t => postnikovMap R f (n + 1) ≫ t)
      (postnikovHomotopyPullbackComparison_path R n hn C)).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
