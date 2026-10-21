module

public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementMap
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFiber

/-!
概要：元の源と fibration 置換の整数 π 群の比較同型は厳密 BF 正方形に自然。
方針：実射の retraction との厳密可換性と、整数 π 上の単位・retraction の往復則を使う。
規約：置換単位の射としての厳密自然性へ強めない。使われ方：元の fiber 長完全列の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

lemma retraction_natural (j : ℤ) (x : homotopyGroup (fibrationReplacement p) j) :
    homotopyMap (fibrationReplacementRetraction q) j (homotopyMap (map p q a b h) j x) =
      homotopyMap a j (homotopyMap (fibrationReplacementRetraction p) j x) := by
  have he := congrArg (fun f => homotopyMap f j) (map_retraction p q a b h)
  rw [homotopyMap_comp, homotopyMap_comp] at he
  exact DFunLike.congr_fun he x

lemma groupEquiv_natural (j : ℤ) (x : homotopyGroup X j) :
    fibrationReplacementGroupEquiv q j (homotopyMap a j x) =
      homotopyMap (map p q a b h) j (fibrationReplacementGroupEquiv p j x) := by
  have hi : Function.Injective (homotopyMap (fibrationReplacementRetraction q) j) :=
    Function.LeftInverse.injective (fibrationReplacementUnit_retraction_map q j)
  apply hi
  change homotopyMap (fibrationReplacementRetraction q) j
      (homotopyMap (fibrationReplacementUnit q) j (homotopyMap a j x)) =
    homotopyMap (fibrationReplacementRetraction q) j
      (homotopyMap (map p q a b h) j (homotopyMap (fibrationReplacementUnit p) j x))
  rw [fibrationReplacementRetraction_unit, retraction_natural,
    fibrationReplacementRetraction_unit]

end SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison
