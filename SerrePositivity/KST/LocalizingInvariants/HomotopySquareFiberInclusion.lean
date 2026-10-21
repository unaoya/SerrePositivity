module

public import SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberGroups

/-!
概要：指定ホモトピーから得た fiber 群の射は、元の包含と源の射にも自然である。
方針：fibration 単位の群同型で比較し、厳密化前後の源の π の一致を使う。
規約：接続射と同じ比較を用いる。使われ方：全 fiber 図式との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.HomotopySquareGroups

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y')
  (γ : (mappingSpace X Y').Edge (vertexOfHom (a ≫ q)) (vertexOfHom (p ≫ b)))

lemma unitFiberEquiv_inclusion (j : ℤ) (x : homotopyGroup (homotopyFiber q) j) :
    homotopyMap (homotopyFiberInclusion (fibrationReplacementProjection q)) j
        (unitFiberEquiv q j x) =
      homotopyMap (fibrationReplacementUnit q) j (homotopyMap (homotopyFiberInclusion q) j x) :=
  (HomotopyFiberComparison.inclusion_natural q (fibrationReplacementProjection q)
    (fibrationReplacementUnit q) (𝟙 Y') (unitSquare q) j x).symm

lemma replacedFiberMap_inclusion (j : ℤ) (x : homotopyGroup (homotopyFiber p) j) :
    homotopyMap (homotopyFiberInclusion (fibrationReplacementProjection q)) j
        (homotopyMap (replacedFiberMap p q a b γ) j x) =
      homotopyMap (a ≫ fibrationReplacementUnit q) j
        (homotopyMap (homotopyFiberInclusion p) j x) := by
  have hh : SpectrumHo.hom (replacedFiberMap p q a b γ ≫
        homotopyFiberInclusion (fibrationReplacementProjection q)) =
      SpectrumHo.hom (homotopyFiberInclusion p ≫ (a ≫ fibrationReplacementUnit q)) := by
    rw [SpectrumHo.hom_comp, SpectrumHo.hom_comp]
    exact HomotopySquareFiber.inclusion_hom _ _ _ _ _ _
  have he := SpectrumHo.homotopyMap_eq_of_hom_eq _ _ hh j
  rw [homotopyMap_comp, homotopyMap_comp] at he
  exact DFunLike.congr_fun he x

lemma inclusion_natural (j : ℤ) (x : homotopyGroup (homotopyFiber p) j) :
    homotopyMap (homotopyFiberInclusion q) j (groupMap p q a b γ j x) =
      homotopyMap a j (homotopyMap (homotopyFiberInclusion p) j x) := by
  apply (fibrationReplacementUnit_piIsomorphism q j).injective
  calc
    _ = homotopyMap (homotopyFiberInclusion (fibrationReplacementProjection q)) j
        (unitFiberEquiv q j (groupMap p q a b γ j x)) :=
      (unitFiberEquiv_inclusion q j _).symm
    _ = homotopyMap (homotopyFiberInclusion (fibrationReplacementProjection q)) j
        (homotopyMap (replacedFiberMap p q a b γ) j x) := by
      change homotopyMap (homotopyFiberInclusion (fibrationReplacementProjection q)) j
        ((unitFiberEquiv q j) ((unitFiberEquiv q j).symm _)) = _
      rw [MulEquiv.apply_symm_apply]
    _ = homotopyMap (a ≫ fibrationReplacementUnit q) j
        (homotopyMap (homotopyFiberInclusion p) j x) :=
      replacedFiberMap_inclusion p q a b γ j x
    _ = _ := by rw [homotopyMap_comp]; rfl

end SerrePositivity.KST.LocalizingInvariants.HomotopySquareGroups
