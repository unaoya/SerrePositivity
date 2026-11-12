module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：任意の厳密 BF 正方形の元の fiber 射を、元の BF fiber 正方形間の全比較へ移す。
方針：通常の cospan の錐比較をホーンと正方形へ制限し、fiber 頂点を照合する。
規約：元の BF 射の類を保持。使われ方：任意の fiber cube との一意性による比較。
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

def squareShape : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} Limits.WalkingCospan))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.{u, u + 1}.inv

lemma squareShape_apex : (squareShape.{u}).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _ := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.{u, u + 1}.inv).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv.app _ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanConeSquareIso_inv_initialVertex]
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (horn 2 2 : SSet.{u + 1}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.{u, u + 1}.inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] _ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
  exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) hi

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def squareHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (X := Sp.{u}) (FiberModel.homotopyFiberSquare p).square
    (FiberModel.homotopyFiberSquare q).square :=
  homPre squareShape (cubeHom p q a b h)

lemma squareHom_apex :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u}) (squareHom p q a b h)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)) =
      Arrow.mk (SpectrumHo.hom (HomotopyFiberComparison.map p q a b h)) := by
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u})
    (homPre squareShape (cubeHom p q a b h)) _) = _
  rw [homPre, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp]
  have hx := congrArg (fun x ↦ Arrow.mk
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u}) (cubeHom p q a b h) x)) squareShape_apex
  exact hx.trans (cubeHom_apex p q a b h)

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison
