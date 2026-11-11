module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberComparisonBase
public import SerrePositivity.KST.LocalizingInvariants.FiberCospanRightShape

/-!
概要：厳密 BF 正方形の元の fiber 比較の右辺を、元の合成三角形と輸送単位で表示する。
方針：全底の共役を第一枝へ制限し、厳密比較の二つの二単体を標準三角形へ戻す。
規約：単位の元の全 prism と端点の等号を保持。使われ方：native な右辺表示との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison

local instance rightPresentationCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def rightUnitIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementProjection p)).edge) :=
  eqToIso (congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k)) (rightDiagram_eq p).symm) ≪≫
    (FiberModel.replacementUnitDiagramIso p).precomp rightShape ≪≫
      eqToIso (congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k))
        (rightDiagram_eq (fibrationReplacementProjection p)))

lemma rightUnitIso_arrow : Arrow.mk (homPre rightShape
    (FiberModel.replacementUnitDiagramIso p).hom) = Arrow.mk (rightUnitIso p).hom := by
  unfold rightUnitIso
  simp only [Iso.trans_hom, eqToIso.hom]
  let f := homPre rightShape (FiberModel.replacementUnitDiagramIso p).hom
  let h₀ := congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k)) (rightDiagram_eq p).symm
  let h₁ := congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k))
    (rightDiagram_eq (fibrationReplacementProjection p))
  change Arrow.mk f = Arrow.mk (eqToHom h₀ ≫ f ≫ eqToHom h₁)
  exact ((arrow_mk_eqToHom_comp h₀ (f ≫ eqToHom h₁)).trans
    (arrow_mk_comp_eqToHom f h₁)).symm

def unitRightPost := StrictArrow.post (CospanReplacement.unit p (fromPoint Y))
  (AsSmall.up.map WalkingCospan.Hom.inl)

def unitRightPre := StrictArrow.pre (CospanReplacement.unit p (fromPoint Y))
  (AsSmall.up.map WalkingCospan.Hom.inl)

lemma rightUnitIso_presentation : Arrow.mk (rightUnitIso p).hom =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (unitRightPost p)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (unitRightPre p))) := by
  rw [← rightUnitIso_arrow]
  change Arrow.mk (homPre rightShape (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (FiberModel.replacementUnitDiagramHomotopy p)))) = _
  rw [rightShape_eq]
  exact StrictArrow.presentation _ _

def replacedTransformation := RawFiberComparison.diagramMap
  (fibrationReplacementProjection p) (fibrationReplacementProjection q)
  (FibrationReplacementComparison.map p q a b h) b
  (FibrationReplacementComparison.map_projection p q a b h).symm

def replacedRightPresentation := Truncated.HomotopyCategory.homMk
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (StrictArrow.post (replacedTransformation p q a b h) (AsSmall.up.map WalkingCospan.Hom.inl))) ≫
  Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (StrictArrow.pre (replacedTransformation p q a b h) (AsSmall.up.map WalkingCospan.Hom.inl)))

lemma replacedRightPresentation_arrow :
    Arrow.mk (homPre rightShape (replacedDiagramHom p q a b h)) =
      Arrow.mk (replacedRightPresentation p q a b h) := by
  rw [rightShape_eq]
  exact StrictArrow.presentation _ _

def rightPresentation := (rightUnitIso p).hom ≫
  replacedRightPresentation p q a b h ≫ (rightUnitIso q).inv

lemma squareHom_right_presentation :
    Arrow.mk (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (squareHom p q a b h)) =
      Arrow.mk (rightPresentation p q a b h) := by
  let e := (FiberModel.replacementUnitDiagramIso q).precomp rightShape
  have hi := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_inv_congr (f := e.hom) (g := (rightUnitIso q).hom)
    (rightUnitIso_arrow q)
  simp only [IsIso.Iso.inv_hom] at hi
  refine (squareHom_right_base p q a b h).trans ?_
  unfold diagramHom
  rw [homPre_homComp, homPre_homComp]
  exact arrow_mk_comp_congr (rightUnitIso_arrow p)
    (arrow_mk_comp_congr (replacedRightPresentation_arrow p q a b h) hi)

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison
