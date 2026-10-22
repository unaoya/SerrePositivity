module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassCospanFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassLayerHomology

/-!
概要：元の class 模型の実射と、元の上段からの準同型比較の厳密な自然性を供給する。
方針：実三成分の模型射と二脚・定数経路の一意性を使う。
規約：関手の射は同じ実模型射。使われ方：元の標的上段を保つ像分解の図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (n : ℤ) (hn : 0 ≤ n) (f : B ⟶ C)

def postnikovClassModelMap : postnikovClassModel R B n hn ⟶ postnikovClassModel R C n hn :=
  HomotopyPullbackModel.map R _ _ _ _ (postnikovPerturbedMap R f n hn)
    (postnikovDerivationTargetMap R f n hn) (postnikovMap R f n)
    (postnikovPerturbedClass_naturality R f n hn)
    (postnikovDerivationTargetMap_zeroSection R f n hn).symm

lemma postnikovClassModelMap_left : postnikovClassModelMap R n hn f ≫
    HomotopyPullbackModel.left R _ _ =
      HomotopyPullbackModel.left R _ _ ≫ postnikovPerturbedMap R f n hn :=
  HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _

lemma postnikovClassModelMap_right : postnikovClassModelMap R n hn f ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ ≫ postnikovMap R f n :=
  HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

lemma postnikovClassModelMap_path : postnikovClassModelMap R n hn f ≫
    HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫
      Path.map R (postnikovDerivationTargetMap R f n hn) :=
  HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

lemma postnikovClassModelFunctor_map {B C : NonpositiveAlgebra R} (f : B ⟶ C) :
    (postnikovClassModelFunctor R n hn).map f = postnikovClassModelMap R n hn f.hom := rfl

lemma postnikovHomotopyPullbackComparison_square : postnikovMap R f (n + 1) ≫
    postnikovHomotopyPullbackComparison R C n hn =
      postnikovHomotopyPullbackComparison R B n hn ≫ postnikovClassModelMap R n hn f := by
  apply HomotopyPullbackModel.hom_ext R (postnikovPerturbedClass R C n hn)
    (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1))
  · rw [Category.assoc, postnikovHomotopyPullbackComparison_left, Category.assoc,
      postnikovClassModelMap_left, ← Category.assoc, postnikovHomotopyPullbackComparison_left]
    exact (postnikovPerturbedInclusion_naturality R f n hn).symm
  · rw [Category.assoc, postnikovHomotopyPullbackComparison_right, Category.assoc,
      postnikovClassModelMap_right, ← Category.assoc, postnikovHomotopyPullbackComparison_right]
    exact postnikovTransition_naturality R B f (n + 1) n (by omega)
  · rw [Category.assoc, postnikovHomotopyPullbackComparison_path, Category.assoc,
      postnikovClassModelMap_path, ← Category.assoc (postnikovHomotopyPullbackComparison R B n hn),
      postnikovHomotopyPullbackComparison_path]
    simp only [Category.assoc, Path.diagonal_naturality]
    rw [← Category.assoc (postnikovMap R f (n + 1)), ← postnikovPerturbedInclusion_naturality,
      Category.assoc, ← Category.assoc (postnikovPerturbedMap R f n hn),
      postnikovPerturbedClass_naturality R f n hn, Category.assoc]

def postnikovClassModelComparison : postnikovFunctor R (n + 1) ⟶
    postnikovClassModelFunctor R n hn where
  app B := postnikovHomotopyPullbackComparison R B.obj n hn
  naturality {_ _} f := postnikovHomotopyPullbackComparison_square R n hn f.hom

lemma postnikovClassModelComparison_quasiIso (B : NonpositiveAlgebra R) :
    QuasiIso ((postnikovClassModelComparison R n hn).app B).hom :=
  postnikovHomotopyPullbackComparison_quasiIso R B.obj n hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
