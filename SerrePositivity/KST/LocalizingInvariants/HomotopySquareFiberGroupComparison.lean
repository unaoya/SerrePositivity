module

public import SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberComparison
public import SerrePositivity.KST.LocalizingInvariants.SpectrumBFPiTransport

/-!
概要：指定 γ からの全 fiber 正方形比較の頂点の整数 π は、構成済みの同じ群比較になる。
方針：元の BF 群との自然な比較で輸送し、同じ単位の逆の群作用を計算する。
規約：元の頂点射と groupMap の選択を保持。使われ方：一般接続射の自然性への移送。
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

local instance squareFiberGroupCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')

lemma unitFiberIso_pi (j : ℤ) : SpectrumHo.bfPiIso (unitFiberIso q) j =
    (HomotopySquareGroups.unitFiberEquiv q j).toCommGrpIso := by
  apply Iso.ext
  exact SpectrumHo.bfPiMap_hom _ j

lemma unitFiberIso_pi_inv (j : ℤ) : SpectrumHo.bfPiMap (unitFiberIso q).inv j =
    CommGrpCat.ofHom (HomotopySquareGroups.unitFiberEquiv q j).symm.toMonoidHom := by
  rw [← SpectrumHo.bfPiIso_inv, unitFiberIso_pi]
  rfl

variable (a : X ⟶ X') (b : Y ⟶ Y')
  (γ : (mappingSpace X Y').Edge (vertexOfHom (a ≫ q)) (vertexOfHom (p ≫ b)))

lemma fiberArrowHom_pi (j : ℤ) : SpectrumHo.bfPiMap (fiberArrowHom p q a b γ) j =
    CommGrpCat.ofHom (HomotopySquareGroups.groupMap p q a b γ j) := by
  rw [fiberArrowHom, SpectrumHo.bfPiMap_comp, SpectrumHo.bfPiMap_hom, unitFiberIso_pi_inv]
  rfl

lemma squareHom_apex_pi (j : ℤ) : Arrow.mk ((SpectrumHo.piFunctor j).map
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (squareHom p q a b γ)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0))) =
    Arrow.mk ((SpectrumHo.piComparison (homotopyFiber p) j).hom ≫
      CommGrpCat.ofHom (HomotopySquareGroups.groupMap p q a b γ j) ≫
        (SpectrumHo.piComparison (homotopyFiber q) j).inv) := by
  have he := congrArg (SpectrumHo.piFunctor j).mapArrow.obj (squareHom_apex p q a b γ)
  have hm := SpectrumHo.piFunctor_map_from_bf (fiberArrowHom p q a b γ) j
  rw [fiberArrowHom_pi] at hm
  exact he.trans (congrArg Arrow.mk hm)

end SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberComparison
