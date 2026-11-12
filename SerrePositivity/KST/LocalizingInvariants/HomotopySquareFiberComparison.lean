module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberComparisonInvertible
public import SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberGroups

/-!
概要：指定 BF 区間 γ から、同じ fiber 群比較を頂点に持つ元の全正方形比較を構成する。
方針：指定区間を持ち上げた厳密正方形の全比較を、標的単位の元の全比較の逆と合成する。
規約：γ と実比較射の選択を保持。使われ方：任意の fiber 図式への接続射の自然性の移送。
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

local instance squareFiberComparisonCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')

def unitSquareIso := HomotopyFiberConeComparison.squareIso q (fibrationReplacementProjection q)
  (fibrationReplacementUnit q) (𝟙 Y') (HomotopySquareGroups.unitSquare q)
  (fibrationReplacementUnit_piIsomorphism q) (by
    intro j
    rw [homotopyMap_id]
    exact Function.bijective_id)

def unitFiberIso : SpectrumHo.obj (homotopyFiber q) ≅
    SpectrumHo.obj (homotopyFiber (fibrationReplacementProjection q)) := by
  haveI : IsIso (SpectrumHo.hom (HomotopySquareGroups.unitFiberMap q)) :=
    isInvertible_of_piIsomorphism _ (HomotopySquareGroups.unitFiberMap_piIsomorphism q)
  exact asIso (SpectrumHo.hom (HomotopySquareGroups.unitFiberMap q))

lemma unitSquareIso_apex : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (unitSquareIso q).hom
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)) =
      Arrow.mk (unitFiberIso q).hom :=
  HomotopyFiberConeComparison.squareHom_apex _ _ _ _ _

lemma unitSquareIso_inv_apex : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (unitSquareIso q).inv
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)) =
      Arrow.mk (unitFiberIso q).inv := by
  let e := functorHomEvaluateIso (unitSquareIso q)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)
  have hi := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_inv_congr (f := e.hom) (g := (unitFiberIso q).hom) (unitSquareIso_apex q)
  simp only [IsIso.Iso.inv_hom] at hi
  exact hi

variable (a : X ⟶ X') (b : Y ⟶ Y')
  (γ : (mappingSpace X Y').Edge (vertexOfHom (a ≫ q)) (vertexOfHom (p ≫ b)))

def lift := HomotopySquareFiber.squareLift p (fibrationReplacementProjection q)
  (a ≫ fibrationReplacementUnit q) b (HomotopySquareGroups.replacedEdge p q a b γ)
  (fibrationReplacementProjection_fibration q)

def strictSquareHom := HomotopyFiberConeComparison.squareHom p (fibrationReplacementProjection q)
  (lift p q a b γ).map b (lift p q a b γ).fac.symm

def squareHom := strictSquareHom p q a b γ ≫ (unitSquareIso q).inv

def fiberArrowHom := SpectrumHo.hom (HomotopySquareGroups.replacedFiberMap p q a b γ) ≫
  (unitFiberIso q).inv

lemma squareHom_apex : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (squareHom p q a b γ)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)) =
      Arrow.mk (fiberArrowHom p q a b γ) := by
  unfold squareHom
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp]
  have hs : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (strictSquareHom p q a b γ)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)) =
      Arrow.mk (SpectrumHo.hom (HomotopySquareGroups.replacedFiberMap p q a b γ)) :=
    HomotopyFiberConeComparison.squareHom_apex _ _ _ _ _
  exact arrow_mk_comp_congr hs (unitSquareIso_inv_apex q)

end SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberComparison
