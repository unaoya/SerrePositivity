module

public import SerrePositivity.KST.LocalizingInvariants.HomotopySquareCanonicalRight
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramModelComparison
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramRelativeNormalization

/-!
概要：任意 fiber 図式の元の全比較を、同じ指定区間の BF 模型比較と同定する。
方針：元の prism と模型の全右辺表示を一致させ、右辺制限の忠実性で戻す。
規約：三頂点だけの可換性から同定しない。使われ方：接続射の一般自然性の移送。
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
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

local instance modelEqualityCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance modelEqualityNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

lemma modelComparison_right_nativePresentation :
    Arrow.mk (rightRestriction.map (modelComparison f)) = Arrow.mk (nativeRightPresentation f) := by
  refine (modelComparison_right f).trans ?_
  rw [HomotopySquareFiberComparison.rightPresentation_canonical]
  rfl

lemma normalizedHom_eq_modelComparison : normalizedHom f = modelComparison f := by
  apply rightRestriction_map_injective
  apply Arrow.mk_injective
  exact (normalizedHom_right_nativePresentation f).trans
    (modelComparison_right_nativePresentation f).symm

lemma normalizedHom_fiber_pi (j : ℤ) :
    Arrow.mk ((SpectrumHo.piFunctor j).map ((vertex 0 0).map (normalizedHom f))) =
    Arrow.mk ((SpectrumHo.piComparison
      (OmegaSpectrum.homotopyFiber (NativeFiber.rightMap D.triangle)) j).hom ≫
      CommGrpCat.ofHom (modelGroupMap f j) ≫
      (SpectrumHo.piComparison
        (OmegaSpectrum.homotopyFiber (NativeFiber.rightMap E.triangle)) j).inv) := by
  rw [normalizedHom_eq_modelComparison]
  exact modelComparison_fiber_pi f j

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
