module
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport

public import SerrePositivity.KST.LocalizingInvariants.RawFiberCubeHom
public import SerrePositivity.KST.LocalizingInvariants.ReplacedFiberConeComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowInverseControl

/-!
概要：長完全列で使う置換済み fiber 射を、元の cospan の全比較を保つ実錐比較へ移す。
方針：実 fiber の cube を保存済みの比較同型で共役し、頂点で可逆比較を相殺する。
規約：頂点の BF 射を選び直さない。使われ方：元の fiber 正方形の全 cube との同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra

namespace SerrePositivity.KST.LocalizingInvariants.ReplacedFiberComparison

local instance replacedCubeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance replacedCubeNerveQuasicategory :
    Quasicategory (SimplicialNerve OmegaSpectrum.{u}) := sp_quasicategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  [hp : ∀ n, Fibration (p.app n).right] [hq : ∀ n, Fibration (q.app n).right]
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def cubeHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (X := Sp.{u}) (FiberModel.replacedCone p).val
    (FiberModel.replacedCone q).val :=
  (FiberModel.replacedConeDiagramIso p).hom ≫ RawFiberComparison.cubeHom p q a b h ≫
    (FiberModel.replacedConeDiagramIso q).inv

lemma cubeHom_comparison : cubeHom p q a b h ≫ (FiberModel.replacedConeDiagramIso q).hom =
    (FiberModel.replacedConeDiagramIso p).hom ≫ RawFiberComparison.cubeHom p q a b h := by
  simp only [cubeHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma cubeHom_apex :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u}) (cubeHom p q a b h) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _)) =
      Arrow.mk (SpectrumHo.hom (FibrationFiberComparison.map p q a b h)) := by
  let : IsIso (SpectrumHo.hom (FiberModel.comparison q hq)) :=
    FiberModel.comparison_isInvertible q hq
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_cancel_comp_right (FiberModel.replacedConeDiagramIso_apex q)
  have he := congrArg (fun α ↦ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u}) α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _))
    (cubeHom_comparison p q a b h)
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp] at he
  have hr := arrow_mk_comp_congr (FiberModel.replacedConeDiagramIso_apex p)
    (RawFiberComparison.cubeHom_apex p q a b h)
  have hf := congrArg SpectrumHo.hom (RawFiberComparison.comparison_natural p q a b h)
  rw [SpectrumHo.hom_comp, SpectrumHo.hom_comp] at hf
  exact (congrArg Arrow.mk he).trans (hr.trans (congrArg Arrow.mk hf.symm))

lemma cubeHom_base : Arrow.mk (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (cubeHom p q a b h)) =
    Arrow.mk (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (RawFiberComparison.cubeHom p q a b h)) := by
  have hp₀ := FiberModel.replacedConeDiagramIso_base p
  have hq₀ := FiberModel.replacedConeDiagramIso_base q
  let e := (FiberModel.replacedConeDiagramIso q).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _)
  have hi := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_inv_congr (f := e.hom) (g := 𝟙 _) hq₀
  simp only [IsIso.Iso.inv_hom, IsIso.inv_id] at hi
  unfold cubeHom
  rw [homPre_homComp, homPre_homComp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity _ _ hp₀).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_right_of_any_identity _ _ hi)

end SerrePositivity.KST.LocalizingInvariants.ReplacedFiberComparison
