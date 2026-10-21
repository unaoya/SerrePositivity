module

public import SerrePositivity.KST.LocalizingInvariants.FibrationBoundaryPointedCompute

/-!
概要：全整数次数の接続準同型は元の BF fibration の厳密可換正方形に自然。
方針：標準基点の一段で計算し、点つき接続射の自然性を整数 π の群同型で戻す。
規約：元の stableConnectingHom を変更しない。使われ方：pro fiber 列の接続射の自然性。
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
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  [hp : ∀ n, Fibration (p.app n).right] [hq : ∀ n, Fibration (q.app n).right]
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)
local instance connectingPFibration (n : ℕ) : Fibration (p.app n).right := hp n
local instance connectingQFibration (n : ℕ) : Fibration (q.app n).right := hq n

lemma stableConnecting_natural (j : ℤ) (x : homotopyGroup Y (j + 1)) :
    homotopyMap (map p q a b h) j (stableConnectingHom p j x) =
      stableConnectingHom q j (homotopyMap b (j + 1) x) := by
  apply (pointedStageEquiv q j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j)).injective
  rw [pointedStageEquiv_natural, stableConnecting_pointed_compute,
    stableConnecting_pointed_compute, positiveStageEquiv_natural]
  exact pointedConnectingHom_natural (p.app (boundaryStage j)) (q.app (boundaryStage j))
    (a.app (boundaryStage j)) (b.app (boundaryStage j))
    (congrArg (fun f => f.app (boundaryStage j)) h) (boundaryIndex j) _

lemma stableConnectingHom_natural (j : ℤ) :
    (homotopyMap (map p q a b h) j).comp (stableConnectingHom p j) =
      (stableConnectingHom q j).comp (homotopyMap b (j + 1)) := by
  apply MonoidHom.ext
  intro x
  exact stableConnecting_natural p q a b h j x

end SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
