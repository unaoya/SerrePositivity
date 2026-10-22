module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageHomology
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionLayerNaturality

/-!
概要：元の隣接上段とその class 模型の層を、同じ係数と元の代数のホモロジーへ同定する。
方針：源の摂動代数の下端消滅を既存の層同型へ渡し、元の準同型比較を合成する。
規約：上段の比較同型を明示し符号を暗黙に変更しない。使われ方：像分解の両射の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

abbrev postnikovClassModel := HomotopyPullbackModel.algebra R (postnikovPerturbedClass R B n hn)
  (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))

def postnikovClassModelLayerHomologyIso :
    (postnikovClassModel R B n hn).X.homology (-(n + 1)) ≅ B.X.homology (-(n + 1)) :=
  SquareZeroExtension.layerHomologyIso (postnikovShiftedLayerBimodule R B n hn 1)
    (postnikovPerturbedClass R B n hn) (-(n + 1))
    (postnikovPerturbedSource_homology_zero R n hn _ (by omega))
    (postnikovPerturbedSource_homology_zero R n hn _ (by omega)) ≪≫
      postnikovShiftedLayerHomologyIso R B n hn 1

def postnikovUpperClassLayerHomologyIso :
    (postnikov R B (n + 1)).X.homology (-(n + 1)) ≅ B.X.homology (-(n + 1)) := by
  have := postnikovHomotopyPullbackComparison_quasiIso R B n hn
  exact asIso (homologyMap (postnikovHomotopyPullbackComparison R B n hn).hom (-(n + 1))) ≪≫
    postnikovClassModelLayerHomologyIso R B n hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
