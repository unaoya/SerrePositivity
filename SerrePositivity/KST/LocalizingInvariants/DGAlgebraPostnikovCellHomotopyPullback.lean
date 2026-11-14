module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovHomotopyPullback
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellDerivation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackSourceQuasiIso

/-!
概要：cell 上の実 Postnikov class の経路模型を、元の隣接拡大と準同型の span で比較。
方針：実 cell lift に沿う模型の射を使い、底への元の遷移も保存する。
規約：非負段の非正次数代数。使われ方：非分裂拡大の具体的 derivation 表示。
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

def postnikovCellHomotopyPullbackComparison :
    HomotopyPullbackModel.algebra R (postnikovCellClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) ⟶
    HomotopyPullbackModel.algebra R (postnikovPerturbedClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) :=
  HomotopyPullbackModel.sourceMap R _ _ (postnikovCellLift R B n hn)

lemma postnikovCellHomotopyPullbackComparison_quasiIso :
    QuasiIso (postnikovCellHomotopyPullbackComparison R B n hn).hom :=
  HomotopyPullbackModel.sourceMap_quasiIso R _ _ _ (postnikovCellLift_quasiIso R B n hn)

lemma postnikovCellHomotopyPullbackComparison_left :
    postnikovCellHomotopyPullbackComparison R B n hn ≫ HomotopyPullbackModel.left R _ _ =
      HomotopyPullbackModel.left R _ _ ≫ postnikovCellLift R B n hn :=
  HomotopyPullbackModel.sourceMap_left R _ _ _

lemma postnikovCellHomotopyPullbackComparison_right :
    postnikovCellHomotopyPullbackComparison R B n hn ≫ HomotopyPullbackModel.right R _ _ =
      HomotopyPullbackModel.right R _ _ :=
  HomotopyPullbackModel.sourceMap_right R _ _ _

lemma postnikovCellHomotopyPullbackComparison_path :
    postnikovCellHomotopyPullbackComparison R B n hn ≫ HomotopyPullbackModel.path R _ _ =
      HomotopyPullbackModel.path R _ _ :=
  HomotopyPullbackModel.sourceMap_path R _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.4.1.28" (partial := component) "仮定：可換環 R 上の厳密非正次数の結合的 dg 代数 B と n≥0（Lean が強い：この E₁ の dg 模型の場合）。結論：τ≤n+1 B→τ≤n B を、cell resolution 上の実導分の class と零切断の homotopy pullback に底への射を保つ準同型の span で比較する（Postnikov 遷移の平方零表示の部分に一致）。一般の Eₖ と HA の普遍 cotangent による導分との比較は含まれない。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovCellHomotopyPullbackComparison_quasiIso
