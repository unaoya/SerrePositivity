module
public import SerrePositivity.KST.SConstruction.PathBoundaryCartesian
public import SerrePositivity.KST.Comparison.SegalRealizationComparison

/-! # 元の経路境界の各行と全対角のホモトピー引き戻し
概要：元の経路境界の各行から全対角への四角形は、正の反復実現後に homotopy pullback。
方針：証明済みの全単体作用素の面条件を Segal の既存の実現定理へ渡す。
規約：未証明の面条件・Kan 性を入力に追加しない。使われ方：零行と既存の homotopy fiber の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.KST.Comparison

/-- 元の反復経路境界の各行から全対角への自然な四角形は homotopy pullback。 -/
lemma iteratedPathBoundary_realization_homotopyPullback (r n : ℕ) (X : StableModel.{u}) :
    IsHomotopyPullback (CommSq.mk
      (diagonalRowEvaluation_naturality (iteratedPathBoundary (r + 1) X) n).symm) :=
  segalRealization_homotopyPullback (iteratedPathBoundary (r + 1) X)
    (fun _ _ θ _ => iteratedPathBoundary_homotopyPullback r X θ) n

end SerrePositivity.KST.SConstruction
