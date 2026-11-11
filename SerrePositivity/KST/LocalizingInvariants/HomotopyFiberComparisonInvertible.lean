module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberRightPresentation
public import SerrePositivity.KST.LocalizingInvariants.ConeHomInvertibility
public import SerrePositivity.KST.LocalizingInvariants.StrictDiagramHomIso
public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementMapInvertible
public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberMapComparison

/-!
概要：源と底が整数 π 同型の厳密 BF 正方形の、元の全 fiber cube 比較を可逆にする。
方針：元の頂点射の五項補題と、同じ底の全 prism の成分の可逆性を錐判定へ渡す。
規約：元の cube と squareHom の類を保持。使われ方：指定 γ の模型比較の標的単位を逆にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison

local instance fiberComparisonInvertibleCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance fiberComparisonInvertibleNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)
  (ha : PiIsomorphism a) (hb : PiIsomorphism b)

include ha hb

lemma replacedTransformation_invertible (i : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((replacedTransformation p q a b h).app i)) := by
  rcases i with ⟨_ | (_ | _)⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge b).toTruncated
    exact isInvertible_of_piIsomorphism b hb
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (FibrationReplacementComparison.map p q a b h)).toTruncated
    exact FibrationReplacementComparison.map_isInvertible p q a b h ha
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{u})).toTruncated
    apply isInvertible_of_piIsomorphism
    intro j
    rw [homotopyMap_id]
    exact Function.bijective_id

lemma replacedDiagramHom_isIso : IsIso (replacedDiagramHom p q a b h) := by
  change IsIso (strictDiagramHomIso (replacedTransformation p q a b h)
    (replacedTransformation_invertible p q a b h ha hb)).hom
  infer_instance

lemma cubeHom_base_isIso : IsIso (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (cubeHom p q a b h)) := by
  haveI := replacedDiagramHom_isIso p q a b h ha hb
  haveI : IsIso (diagramHom p q a b h) := by
    unfold diagramHom
    infer_instance
  exact isIso_of_arrow_mk_eq (cubeHom_base p q a b h)

lemma cubeHom_isIso : IsIso (cubeHom p q a b h) := by
  haveI : IsIso (SpectrumHo.hom (HomotopyFiberComparison.map p q a b h)) :=
    HomotopyFiberComparison.map_isInvertible p q a b h ha hb
  apply coneHom_isIso_of_apex_base
  · exact isIso_of_arrow_mk_eq (cubeHom_apex p q a b h)
  · exact cubeHom_base_isIso p q a b h ha hb

lemma squareHom_isIso : IsIso (squareHom p q a b h) := by
  haveI := cubeHom_isIso p q a b h ha hb
  unfold squareHom homPre
  infer_instance

def squareIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Y := Sp.{u}) (FiberModel.homotopyFiberSquare p).square
    (FiberModel.homotopyFiberSquare q).square := by
  haveI := squareHom_isIso p q a b h ha hb
  exact asIso (squareHom p q a b h)

lemma squareIso_hom : (squareIso p q a b h ha hb).hom = squareHom p q a b h := rfl

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison
