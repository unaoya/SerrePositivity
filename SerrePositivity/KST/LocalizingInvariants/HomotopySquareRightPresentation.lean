module

public import SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberGroupComparison

/-!
概要：指定 γ の模型 fiber 比較の全右辺を、同じ厳密化と標的単位の標準表示で記述する。
方針：指定 PathLift の全比較と標的単位の逆を右辺へ制限し、構成済みの標準表示を使う。
規約：squareHom と groupMap の同じ選択を保持。使われ方：nativeRightPresentation との貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberComparison

local instance squareRightPresentationCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')

def unitRightIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementProjection q)).edge) := by
  let e := (unitSquareIso q).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge
  haveI : IsIso (HomotopyFiberConeComparison.rightPresentation q
      (fibrationReplacementProjection q) (fibrationReplacementUnit q) (𝟙 Y')
      (HomotopySquareGroups.unitSquare q)) :=
    isIso_of_arrow_mk_eq (f := HomotopyFiberConeComparison.rightPresentation q
      (fibrationReplacementProjection q) (fibrationReplacementUnit q) (𝟙 Y')
      (HomotopySquareGroups.unitSquare q)) (g := e.hom)
      (HomotopyFiberConeComparison.squareHom_right_presentation _ _ _ _ _).symm
  exact asIso (HomotopyFiberConeComparison.rightPresentation q
    (fibrationReplacementProjection q) (fibrationReplacementUnit q) (𝟙 Y')
    (HomotopySquareGroups.unitSquare q))

lemma unitRightIso_arrow : Arrow.mk (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (unitSquareIso q).hom) =
    Arrow.mk (unitRightIso q).hom :=
  HomotopyFiberConeComparison.squareHom_right_presentation _ _ _ _ _

lemma unitRightIso_inv_arrow : Arrow.mk (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (unitSquareIso q).inv) =
    Arrow.mk (unitRightIso q).inv := by
  let e := (unitSquareIso q).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge
  have hi := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_inv_congr (f := e.hom) (g := (unitRightIso q).hom) (unitRightIso_arrow q)
  simp only [IsIso.Iso.inv_hom] at hi
  exact hi

variable (a : X ⟶ X') (b : Y ⟶ Y')
  (γ : (mappingSpace X Y').Edge (vertexOfHom (a ≫ q)) (vertexOfHom (p ≫ b)))

def rightPresentation := HomotopyFiberConeComparison.rightPresentation p
  (fibrationReplacementProjection q) (lift p q a b γ).map b (lift p q a b γ).fac.symm ≫
    (unitRightIso q).inv

lemma squareHom_right_presentation :
    Arrow.mk (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (squareHom p q a b γ)) =
      Arrow.mk (rightPresentation p q a b γ) := by
  unfold squareHom
  rw [homPre_homComp]
  exact arrow_mk_comp_congr (HomotopyFiberConeComparison.squareHom_right_presentation _ _ _ _ _)
    (unitRightIso_inv_arrow q)

end SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberComparison
