module

public import SerrePositivity.KST.LocalizingInvariants.FibrationFiberStageNaturality
public import SerrePositivity.KST.Spectra.SpectrumBoundary

/-!
概要：整数次数の接続射を、標準基点での元の点つき fibration の接続射で計算する。
方針：fiberPoint への二つの基点輸送を同じ群同型で比較して消去する。
規約：計算段は元の boundaryStage。使われ方：接続射の厳密正方形への自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
  [hp : ∀ n, Fibration (p.app n).right]
local instance boundaryPointedFibration (n : ℕ) : Fibration (p.app n).right := hp n

lemma stableConnecting_pointed_compute (j : ℤ) (x : homotopyGroup Y (j + 1)) :
    pointedStageEquiv p j (boundaryStage j) (boundaryIndex j)
      (boundaryStage_admissible j) (boundaryStage_degree j) (stableConnectingHom p j x) =
        pointedConnectingHom (p.app (boundaryStage j)) (boundaryIndex j)
          (positiveStageEquiv Y (j + 1) (boundaryStage j) (boundaryIndex j + 1)
            (boundaryStage_succ_admissible j) (boundaryStage_succ_degree j) x) := by
  apply (pointedFiberGroupEquiv (p.app (boundaryStage j)) (boundaryIndex j)).injective
  rw [pointedStageEquiv_transport, pointedConnectingHom_compute]
  exact stableConnectingHom_compute p j x

end SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
