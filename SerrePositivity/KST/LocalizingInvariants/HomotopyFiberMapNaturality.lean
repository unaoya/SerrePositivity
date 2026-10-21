module

public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementMap
public import SerrePositivity.KST.LocalizingInvariants.FibrationConnectingNaturality
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFiber

/-!
概要：任意の厳密 BF 正方形から元の homotopy fiber 間の実射と接続射の自然性を得る。
方針：mapping path の置換比較を fibration の fiber 比較へ渡し、両射影との可換性を戻す。
規約：元の homotopyFiberBoundary を使用。使われ方：任意の実 fiber 図式への自然性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyFiberComparison
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def map : homotopyFiber p ⟶ homotopyFiber q :=
  FibrationFiberComparison.map (fibrationReplacementProjection p) (fibrationReplacementProjection q)
    (FibrationReplacementComparison.map p q a b h) b
    (FibrationReplacementComparison.map_projection p q a b h).symm

lemma map_inclusion : map p q a b h ≫ homotopyFiberInclusion q =
    homotopyFiberInclusion p ≫ a := by
  change FibrationFiberComparison.map _ _ _ _ _ ≫
    (fiberInclusion (fibrationReplacementProjection q) _ ≫ fibrationReplacementRetraction q) = _
  rw [← Category.assoc, FibrationFiberComparison.map_inclusion, Category.assoc,
    FibrationReplacementComparison.map_retraction, ← Category.assoc]
  rfl

lemma boundary_natural (j : ℤ) (x : homotopyGroup Y (j + 1)) :
    homotopyMap (map p q a b h) j (homotopyFiberBoundary p j x) =
      homotopyFiberBoundary q j (homotopyMap b (j + 1) x) :=
  FibrationFiberComparison.stableConnecting_natural (fibrationReplacementProjection p)
    (fibrationReplacementProjection q) (FibrationReplacementComparison.map p q a b h) b
    (FibrationReplacementComparison.map_projection p q a b h).symm j x

lemma boundaryHom_natural (j : ℤ) :
    (homotopyMap (map p q a b h) j).comp (homotopyFiberBoundary p j) =
      (homotopyFiberBoundary q j).comp (homotopyMap b (j + 1)) := by
  apply MonoidHom.ext
  intro x
  exact boundary_natural p q a b h j x

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberComparison
