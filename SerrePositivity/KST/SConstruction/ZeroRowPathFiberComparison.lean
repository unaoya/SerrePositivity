module
public import SerrePositivity.KST.SConstruction.ZeroRowKanFiberSquare
public import SerrePositivity.KST.SConstruction.StrictZeroPathFiberComparison

/-! # 元の反復経路零行と既存の path homotopy fiber の比較
概要：元の零行から既存の点つき反復境界の path homotopy fiber へ実際の局所化同型を構成する。
方針：境界の厳密な零合成と零行の homotopy pullback 四角形を定数 path による比較へ渡す。
規約：零行自身の Kan 性は要求しない。使われ方：前の反復実現と fiber の点つき比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel
open Spectra
open scoped Simplicial

/-- 元の反復経路零行から既存の path homotopy fiber の底への定数 path による比較。 -/
def zeroRowPathFiberComparison (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⟶
      (iteratedPathHomotopyFiber r X).right :=
  strictZeroPathFiberMap (pointedFullIteratedPathKanBoundary r X)
    (zeroRowPathToKan r X) (zeroRowPathToKan_boundary r X)

/-- 零行から既存の fiber への比較は元の Kan 全空間への評価を回収する。 -/
lemma zeroRowPathFiberComparison_projection (r : ℕ) (X : StableModel.{u}) :
    zeroRowPathFiberComparison r X ≫
      (pathHomotopyFiberProjection (pointedFullIteratedPathKanBoundary r X)).right =
        zeroRowPathToKan r X :=
  strictZeroPathFiberMap_projection _ _ _

/-- 元の零行と既存の path homotopy fiber の比較は全ての正の反復で局所化同型。 -/
lemma zeroRowPathFiberComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (zeroRowPathFiberComparison (r + 1) X)) :=
  strictZeroPathFiberMap_localized_isIso_of_homotopyPullback
    (pointedFullIteratedPathKanBoundary (r + 1) X) (zeroRowPathToKan (r + 1) X)
    (zeroRowPathToKan_boundary (r + 1) X) (zeroRowKanBoundary_homotopyPullback r X)

end SerrePositivity.KST.SConstruction
