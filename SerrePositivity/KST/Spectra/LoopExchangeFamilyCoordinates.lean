module

public import SerrePositivity.KST.Spectra.LoopExchangeFamilyTrace
public import SerrePositivity.KST.Spectra.DeloopedExchangeSquareCoordinates

/-!
概要：任意の同じ内側の源に対する随伴の厳密可換式を、二重後合成へ移す。
方針：元の二重内部 Hom の合成保存を使う。
規約：移送区間の選択は不要。使われ方：交換族の移送自然性の共通終辺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.LoopExchangeFamily
open LoopExchangePaths

/-- 元の内側の源の随伴可換式は、同じ二重後合成の厳密可換式となる。 -/
lemma doublePost_square {S Y Y' Z Z' : PointedSimplicialSet.{u}}
    (h : Y ⟶ PointedObject.basedHom S Z) (h' : Y' ⟶ PointedObject.basedHom S Z')
    (v : Y ⟶ Y') (w : Z ⟶ Z')
    (hc : h ≫ PointedObject.basedHomMap S w = v ≫ h') :
    doublePost h ≫ TwoLoopSource.loopPost S w = doublePost v ≫ doublePost h' := by
  change doublePost h ≫ doublePost (PointedObject.basedHomMap S w) = _
  rw [doublePost_comp, doublePost_comp, hc]

end SerrePositivity.KST.Spectra.LoopExchangeFamily
