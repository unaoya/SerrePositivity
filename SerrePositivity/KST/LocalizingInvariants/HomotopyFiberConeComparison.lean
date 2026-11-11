module

public import SerrePositivity.KST.LocalizingInvariants.ReplacedFiberCubeHom
public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeTransportIso
public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberMapNaturality

/-!
概要：任意の厳密 BF 正方形の元の homotopy fiber 射を、全錐比較の頂点に実現する。
方針：置換後の実 cube を、頂点で恒等となる指定輸送同型で共役する。
規約：底は輸送単位を含む全図式比較として保持。使われ方：指定 prism と同じ比較への照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra

namespace SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison

local instance homotopyCubeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def replacedHom := ReplacedFiberComparison.cubeHom
  (OmegaSpectrum.fibrationReplacementProjection p) (OmegaSpectrum.fibrationReplacementProjection q)
  (FibrationReplacementComparison.map p q a b h) b
  (FibrationReplacementComparison.map_projection p q a b h).symm

def cubeHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (X := Sp.{u}) (FiberModel.homotopyFiberCone p).val
    (FiberModel.homotopyFiberCone q).val :=
  (FiberModel.homotopyFiberConeTransportIso p).hom ≫ replacedHom p q a b h ≫
    (FiberModel.homotopyFiberConeTransportIso q).inv

lemma cubeHom_comparison : cubeHom p q a b h ≫
    (FiberModel.homotopyFiberConeTransportIso q).hom =
      (FiberModel.homotopyFiberConeTransportIso p).hom ≫ replacedHom p q a b h := by
  simp only [cubeHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma cubeHom_apex :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u}) (cubeHom p q a b h) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _)) =
      Arrow.mk (SpectrumHo.hom (HomotopyFiberComparison.map p q a b h)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_cancel_comp_right (FiberModel.homotopyFiberConeTransportIso_apex q)
  have he := congrArg (fun α ↦ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u}) α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _))
    (cubeHom_comparison p q a b h)
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp] at he
  have hr := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u}) (FiberModel.homotopyFiberConeTransportIso p).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u}) (replacedHom p q a b h) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _))
    (FiberModel.homotopyFiberConeTransportIso_apex p)
  have hs := ReplacedFiberComparison.cubeHom_apex
    (OmegaSpectrum.fibrationReplacementProjection p)
    (OmegaSpectrum.fibrationReplacementProjection q)
    (FibrationReplacementComparison.map p q a b h) b
    (FibrationReplacementComparison.map_projection p q a b h).symm
  exact (congrArg Arrow.mk he).trans
    (hr.trans (hs.trans (congrArg Arrow.mk (Category.comp_id _).symm)))

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison
