module

public import SerrePositivity.KST.Comparison.SegalRealizationComparison
public import SerrePositivity.KST.Comparison.BarZeroEvaluation
public import SerrePositivity.KST.Comparison.RegularBarFiber

/-!
# 群状モノイドの正則 bar 束のホモトピーファイバー

概要：群状単体的モノイドは、正則 bar 束の基点上のホモトピーファイバーである。
方針：全ての単体作用の比較に Segal Proposition 1.6 を適用し、第零行の同型で標準四角形へ移す。
規約：Segal 1974 Propositions 1.5・1.6、KST Lemma 2.13。各次数が群であることは要求しない。
使われ方：収縮する全空間から基点ループ空間への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
open SerrePositivity.BisimplicialModel

/--
概要：転置した正則 bar の対角の射影は元の正則 bar の射影と一致する。
方針：両方の次数で同じ射列のラベルを読むことを使う。
規約：対角の転置の同型を両側に明示する。
使われ方：第零行の四角形の標準 bar 束への移送。
-/
theorem actionBarProjection_diagonal (M : SimplicialObject MonCat.{u}) :
    diagonal.map (actionBarProjection M) ≫ (diagonalFlipIso (bisimplicialBar M)).hom =
      (diagonalFlipIso (bisimplicialRegularBar M)).hom ≫ regularBarProjection M := rfl

/--
概要：群状モノイドの標準ファイバーの四角形はホモトピー引き戻しである。
方針：面の自然性の比較を realization へ送り、第零行をモノイドと一点へ同定する。
規約：Segal 1974 Proposition 1.5 のファイバー比較。モノイドの Kan 性は不要。
使われ方：標準の群完備化写像の局所化可逆性。
-/
theorem regularBarFiber_homotopyPullback (M : SimplicialObject MonCat.{u})
    (hG : SimplicialMonoid.IsGrouplike M) :
    IsHomotopyPullback (regularBarFiber_isPullback M).toCommSq := by
  have h := segalRealization_homotopyPullback (actionBarProjection M) (fun r k θ _ =>
    (isHomotopyPullback_flip_iff (actionBarSquare M θ.op)).mpr
      (actionBarSquare_isHomotopyPullback M hG θ.op)) 0
  let eP := simplexZeroTensorIso ((actionBarTotal M).obj (op ⦋0⦌)) ≪≫ regularBarZeroRowIso M
  let eY := simplexZeroTensorIso ((actionBarBase M).obj (op ⦋0⦌)) ≪≫ monoidBarZeroRowIso M
  apply (isHomotopyPullback_iff_of_localized_isIso
    (CommSq.mk (diagonalRowEvaluation_naturality (actionBarProjection M) 0).symm)
    (regularBarFiber_isPullback M).toCommSq eP.hom
    (diagonalFlipIso (bisimplicialRegularBar M)).hom eY.hom
    (diagonalFlipIso (bisimplicialBar M)).hom ?_ ?_ ?_ ?_
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mp h
  · exact regularBarZeroRow_evaluation M
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · exact actionBarProjection_diagonal M
  · exact monoidBarZeroRow_evaluation M

end SerrePositivity.KST.Comparison
