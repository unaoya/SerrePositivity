module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovAlgebraPullback
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackComparisonQuasiIso

/-!
概要：元の Postnikov 上段から、実 class と零切断の homotopy pullback 模型へ準同型比較。
方針：class の次数全射性と通常 pullback 比較の準同型性を、元の実代数同型へ合成する。
規約：元の包含と遷移の二脚を保持。使われ方：LT の非分裂拡大の模型比較。
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

lemma postnikovPerturbedClass_epi : Epi (postnikovPerturbedClass R B n hn).hom := by
  let t := biprod.map (postnikovTransition R B (n + 1) n (by omega)).hom
    (-(𝟙 ((postnikovLayerBimodule R B n).X⟦(1 : ℤ)⟧)))
  have : Epi t := by dsimp [t]; infer_instance
  apply epi_of_epi_f
  intro p
  have he : Epi (t.f p) := inferInstance
  have ht : (postnikovPerturbedClass R B n hn).hom.f p = t.f p :=
    postnikovPerturbedClass_f R B n hn p
  exact ht.symm ▸ he

def postnikovHomotopyPullbackComparison : postnikov R B (n + 1) ⟶
    HomotopyPullbackModel.algebra R (postnikovPerturbedClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) :=
  (postnikovStrictPullbackIso R B n hn).hom ≫ HomotopyPullbackModel.comparison R _ _

lemma postnikovHomotopyPullbackComparison_quasiIso :
    QuasiIso (postnikovHomotopyPullbackComparison R B n hn).hom := by
  have := postnikovPerturbedClass_epi R B n hn
  change QuasiIso ((postnikovStrictPullbackIso R B n hn).hom.hom ≫
    (HomotopyPullbackModel.comparison R _ _).hom)
  exact quasiIso_comp _ _
    (hφ := quasiIso_of_isIso ((Mon.forget (Complex R)).mapIso
      (postnikovStrictPullbackIso R B n hn)).hom)
    (hφ' := HomotopyPullbackModel.comparison_quasiIso_left R _ _)

lemma postnikovHomotopyPullbackComparison_left : postnikovHomotopyPullbackComparison R B n hn ≫
    HomotopyPullbackModel.left R _ _ = postnikovPerturbedInclusion R B n hn := by
  rw [postnikovHomotopyPullbackComparison, Category.assoc,
    HomotopyPullbackModel.comparison_left, postnikovStrictPullbackIso_fst]

lemma postnikovHomotopyPullbackComparison_right : postnikovHomotopyPullbackComparison R B n hn ≫
    HomotopyPullbackModel.right R _ _ = postnikovTransition R B (n + 1) n (by omega) := by
  rw [postnikovHomotopyPullbackComparison, Category.assoc,
    HomotopyPullbackModel.comparison_right, postnikovStrictPullbackIso_snd]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.4.1.28" (partial := component) "仮定：可換環 R 上の厳密非正次数の結合的 dg 代数 B と n≥0（Lean が強い：この E₁ の dg 模型の場合）。結論：τ≤n+1 B→τ≤n B を、cell resolution 上の実導分の class と零切断の homotopy pullback に底への射を保つ準同型の span で比較する（Postnikov 遷移の平方零表示の部分に一致）。一般の Eₖ と HA の普遍 cotangent による導分との比較は含まれない。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovHomotopyPullbackComparison_quasiIso
attribute [cite HA "7.4.1.28" (partial := component) "仮定：可換環 R 上の厳密非正次数の結合的 dg 代数 B と n≥0（Lean が強い：この E₁ の dg 模型の場合）。結論：τ≤n+1 B→τ≤n B を、cell resolution 上の実導分の class と零切断の homotopy pullback に底への射を保つ準同型の span で比較する（Postnikov 遷移の平方零表示の部分に一致）。一般の Eₖ と HA の普遍 cotangent による導分との比較は含まれない。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovHomotopyPullbackComparison_right
