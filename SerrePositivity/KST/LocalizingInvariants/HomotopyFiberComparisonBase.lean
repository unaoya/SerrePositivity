module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberRightShape
public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementUnitDiagramIso

/-!
概要：元の homotopy fiber の全 cube の底を、置換単位と厳密 cospan 比較の共役で表示する。
方針：実 cube を図式側へ制限し、置換比較の恒等性と同じ単位 prism の類を使う。
規約：元の全 h Fun 射を Arrow 等号で保持。使われ方：模型の右辺と標準三角形の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def replacedDiagramHom := Truncated.HomotopyCategory.homMk
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (RawFiberComparison.diagramHomotopy
    (OmegaSpectrum.fibrationReplacementProjection p)
    (OmegaSpectrum.fibrationReplacementProjection q)
    (FibrationReplacementComparison.map p q a b h) b
    (FibrationReplacementComparison.map_projection p q a b h).symm))

def diagramHom := (FiberModel.replacementUnitDiagramIso p).hom ≫
  replacedDiagramHom p q a b h ≫ (FiberModel.replacementUnitDiagramIso q).inv

lemma replacedHom_base : Arrow.mk (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (replacedHom p q a b h)) =
    Arrow.mk (replacedDiagramHom p q a b h) := by
  exact (ReplacedFiberComparison.cubeHom_base
    (OmegaSpectrum.fibrationReplacementProjection p)
    (OmegaSpectrum.fibrationReplacementProjection q)
    (FibrationReplacementComparison.map p q a b h) b
    (FibrationReplacementComparison.map_projection p q a b h).symm).trans
      (RawFiberComparison.cubeHom_base _ _ _ _ _)

lemma cubeHom_base : Arrow.mk (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (cubeHom p q a b h)) =
    Arrow.mk (diagramHom p q a b h) := by
  let e := (FiberModel.homotopyFiberConeTransportIso q).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _)
  have hi := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_inv_congr (f := e.hom)
    (g := (FiberModel.replacementUnitDiagramIso q).hom)
    (FiberModel.homotopyFiberConeTransportIso_base q)
  simp only [IsIso.Iso.inv_hom] at hi
  unfold cubeHom
  rw [homPre_homComp, homPre_homComp]
  exact arrow_mk_comp_congr (FiberModel.homotopyFiberConeTransportIso_base p)
    (arrow_mk_comp_congr (replacedHom_base p q a b h) hi)

lemma squareHom_right_base : Arrow.mk (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (squareHom p q a b h)) =
    Arrow.mk (homPre rightShape (diagramHom p q a b h)) :=
  (squareHom_right p q a b h).trans (homPre_arrow_congr rightShape (cubeHom_base p q a b h))

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison
