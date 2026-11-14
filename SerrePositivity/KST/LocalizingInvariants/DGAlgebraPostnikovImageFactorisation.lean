module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageFactorisation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackProjectionQuasiIso

/-!
概要：元の隣接上段の射を、像拡大と準同型な実代数を通る二射へ厳密に因子分解する。
方針：源の像拡大と標的上段の準同型比較を経路模型で引き戻し、元の可換式を持ち上げる。
規約：終域は元の標的上段そのもの。使われ方：LT Lemma 2.30 の実レベル因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

abbrev postnikovImageFactorisationObject := HomotopyPullbackModel.algebra R
  (postnikovSourceImageToTarget R f n hn) (postnikovHomotopyPullbackComparison R C n hn)

abbrev postnikovImageFactorisationComparison : postnikovImageFactorisationObject R f n hn ⟶
    postnikovSourceImageExtension R f n hn := HomotopyPullbackModel.left R _ _

abbrev postnikovImageFactorisationTarget : postnikovImageFactorisationObject R f n hn ⟶
    postnikov R C (n + 1) := HomotopyPullbackModel.right R _ _

lemma postnikovImageFactorisationComparison_quasiIso :
    QuasiIso (postnikovImageFactorisationComparison R f n hn).hom :=
  HomotopyPullbackModel.left_quasiIso R _ _
    (postnikovHomotopyPullbackComparison_quasiIso R C n hn)

def postnikovImageFactorisationWitness : Path.Witness R
    (postnikovSourceImageFactor R f n hn ≫ postnikovSourceImageToTarget R f n hn)
    (postnikovMap R f (n + 1) ≫ postnikovHomotopyPullbackComparison R C n hn) where
  hom := postnikovSourceImageFactor R f n hn ≫ postnikovSourceImageToTarget R f n hn ≫
    Path.diagonal R _
  source_eq := by rw [Category.assoc, Category.assoc, Path.diagonal_source, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Category.assoc, Path.diagonal_target, Category.comp_id]
    exact postnikovSourceImageFactorisation R f n hn

def postnikovImageFactorisationSource : postnikov R B (n + 1) ⟶
    postnikovImageFactorisationObject R f n hn :=
  HomotopyPullbackModel.lift R _ _ (postnikovSourceImageFactor R f n hn)
    (postnikovMap R f (n + 1)) (postnikovImageFactorisationWitness R f n hn)

lemma postnikovImageFactorisationSource_comparison : postnikovImageFactorisationSource R f n hn ≫
    postnikovImageFactorisationComparison R f n hn = postnikovSourceImageFactor R f n hn :=
  HomotopyPullbackModel.lift_left R _ _ _ _ _

lemma postnikovImageFactorisation_fac : postnikovImageFactorisationSource R f n hn ≫
    postnikovImageFactorisationTarget R f n hn = postnikovMap R f (n + 1) :=
  HomotopyPullbackModel.lift_right R _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Lemma 2.30" (partial := component) "仮定：可換基礎環上の非正 dg 代数の自然数塔、n≥1（Lean が強い）。結論：Postnikov 切断からレベルごとに連結な左脚とプロ同値な右脚の因子分解。一般の Pro(Alg^cn) の同値表示は範囲外（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovImageFactorisationComparison_quasiIso
