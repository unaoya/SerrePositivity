module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramNormalization
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramRightRestriction
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramNativeRightPresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowInverseControl

/-!
概要：接続射と共有する相対正規化は、元の右辺の全 h Fun 比較を変えない。
方針：相対比較の右辺恒等を回収し、元の射を共役した際の左右の恒等を相殺する。
規約：選択する型の相対条件を使う。使われ方：normalizedHom と指定模型比較の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

local instance relativeNormalizationCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance relativeNormalizationNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

lemma normalized_right_map (D : FiberDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (normalized D).triangle.square = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ D.triangle.square :=
  (FiberModel.homotopyFiberSquare (NativeFiber.rightMap D.triangle)).right_edge.trans
    (NativeFiber.asFiberSquare D.triangle D.isFiber).right_edge.symm

lemma normalization_right_arrow (D : FiberDiagram.{u}) :
    Arrow.mk (rightRestriction.map (normalization D).hom) =
      Arrow.mk (𝟙 (rightRestriction.obj D)) := by
  have hr := (FiberComparison.relativeFunctorIso
    (NativeFiber.asFiberSquare D.triangle D.isFiber)
    (FiberModel.homotopyFiberSquare (NativeFiber.rightMap D.triangle))).right_arrow
  have ho : rightRestriction.obj D = HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (NativeFiber.rightMap D.triangle)).edge)) :=
    congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k))
      (NativeFiber.asFiberSquare D.triangle D.isFiber).right_edge
  exact hr.trans (congrArg (fun x ↦ Arrow.mk (𝟙 x)) ho.symm)

lemma normalization_inv_right_arrow (D : FiberDiagram.{u}) :
    Arrow.mk (rightRestriction.map (normalization D).inv) =
      Arrow.mk (𝟙 (rightRestriction.obj D)) := by
  let e := rightRestriction.mapIso (normalization D)
  have hi := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_inv_congr (f := e.hom) (g := 𝟙 (rightRestriction.obj D))
    (normalization_right_arrow D)
  simp only [IsIso.Iso.inv_hom, IsIso.inv_id] at hi
  exact hi

lemma normalizedHom_right_arrow {D E : FiberDiagram.{u}} (f : D ⟶ E) :
    Arrow.mk (rightRestriction.map (normalizedHom f)) = Arrow.mk (rightRestriction.map f) := by
  rw [normalizedHom, Functor.map_comp, Functor.map_comp]
  have h₀ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity
    (rightRestriction.map (normalization D).inv)
    (rightRestriction.map f ≫ rightRestriction.map (normalization E).hom)
    (normalization_inv_right_arrow D)
  exact h₀.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_right_of_any_identity _ _ (normalization_right_arrow E))

lemma normalizedHom_right_nativePresentation {D E : FiberDiagram.{u}} (f : D ⟶ E) :
    Arrow.mk (rightRestriction.map (normalizedHom f)) = Arrow.mk (nativeRightPresentation f) :=
  (normalizedHom_right_arrow f).trans (rightRestriction_nativePresentation f)

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
