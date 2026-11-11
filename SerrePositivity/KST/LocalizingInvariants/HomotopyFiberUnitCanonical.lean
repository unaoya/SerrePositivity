module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberRightPresentation
public import SerrePositivity.KST.LocalizingInvariants.SpectrumCompositionIdentity

/-!
概要：元の fiber 置換単位の全右辺を、単位と射影の標準上側三角形へ同定する。
方針：元の prism の二三角形表示を使い、下側の恒等射因子だけを消す。
規約：元の単位の全類を保持。使われ方：模型右辺の単位と逆単位の相殺。
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
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison

local instance unitCanonicalCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)

lemma unitRightPost_identity : Arrow.mk (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (unitRightPost p))) =
    Arrow.mk (𝟙 (HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p).edge)))) := by
  exact SpectrumTriangleNormalization.canonicalPost_identity_arrow p

lemma unitRightPre_canonical : Arrow.mk (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (unitRightPre p))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (SpectrumTriangleNormalization.canonicalPre
        (fibrationReplacementUnit p) (fibrationReplacementProjection p)))) := by
  apply HomotopyArrow.congr
  unfold unitRightPre StrictArrow.pre
  rw [HomotopyArrow.rebase_map]
  rfl

lemma rightUnitIso_canonical : Arrow.mk (rightUnitIso p).hom =
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (SpectrumTriangleNormalization.canonicalPre
        (fibrationReplacementUnit p) (fibrationReplacementProjection p)))) := by
  exact (rightUnitIso_presentation p).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity _ _ (unitRightPost_identity p)).trans
      (unitRightPre_canonical p))

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison
