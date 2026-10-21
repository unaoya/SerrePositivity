module

public import SerrePositivity.KST.LocalizingInvariants.CospanConeSquareLegs
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeLegs

/-!
概要：通常の BF cospan の strict 錐を、同じ頂点・二射・二脚を持つ実正方形へ移す。
方針：cospan の horn 表示へ制限し、元の strict な錐の脚の計算と照合する。
規約：極限性の証人も移送する。使われ方：積射影の基底変換の実 pullback 正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.StrictCospanCone
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (A B : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom A B) :=
  OmegaSpectrum.mappingSpace_kanComplex A B
variable {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
  (c : Cone (spectrumPullbackDiagram f g))

def hornCone : JoinCone (edgeCospan (coherentNerveEdge f).toTruncated
    (coherentNerveEdge g).toTruncated) :=
  (DiagramLimitTransport.restrict (strictCoherentCone c)
    CospanShape.strictCospanHornIso.inv).cast (CospanShape.strictDiagram_eq f g)

lemma hornCone_isLimit (hc : IsLimitCone (strictCoherentCone c)) :
    IsLimitCone (hornCone f g c) := by
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have := DiagramLimitTransport.restriction_trivial
    (strictCoherentDiagram (spectrumPullbackDiagram f g)) i
    (isPrecompositionEquivalence_of_iso CospanShape.strictCospanHornIso.symm)
  let e := qCatEquivalenceOfTrivialKanFibration
    (sliceOverRestrict (strictCoherentDiagram (spectrumPullbackDiagram f g)) i)
  have ht : IsLimitCone (DiagramLimitTransport.restrict (strictCoherentCone c) i) :=
    (e.isTerminalVertex_iff (strictCoherentCone c)).1 hc
  exact ht.cast (CospanShape.strictDiagram_eq f g)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := coneSquare (hornCone f g c)

lemma square_isPullback (hc : IsLimitCone (strictCoherentCone c)) :
    IsPullbackSquare (square f g c) := coneSquare_isPullback _ (hornCone_isLimit f g c hc)

lemma square_right : squareRightEdge ≫ square f g c =
    SSet.yonedaEquiv.symm (coherentNerveEdge f).edge := by
  rw [square, coneSquare_right, edgeCospan_left]
  rfl

lemma square_top : squareTopEdge ≫ square f g c =
    SSet.yonedaEquiv.symm (coherentNerveEdge g).edge := by
  rw [square, coneSquare_top, edgeCospan_right]
  rfl

lemma square_vertex : squareVertex (square f g c) 0 0 = coherentNerveVertex c.pt := by
  rw [square, FiberModel.coneSquare_apex, hornCone, JoinCone.vertex_cast,
    DiagramLimitTransport.vertex_restrict, strictCoherentCone_vertex]

end SerrePositivity.KST.LocalizingInvariants.StrictCospanCone
