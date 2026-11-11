module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberCanonicalSquare
public import SerrePositivity.KST.LocalizingInvariants.HomotopySquareRightPresentation
public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingArrowCongruence

/-!
概要：指定 BF 区間の模型 fiber 比較の全右辺を、置換前の三角形と同じ区間へ戻す。
方針：厳密化した比較の標準表示に PathLift の全自然性を適用し、標的単位を相殺する。
規約：元の squareHom と γ を保持。使われ方：任意 fiber 図式の元の全比較との一致。
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

local instance canonicalRightCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance canonicalRightNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')

lemma unitRightIso_hom_triangle : (unitRightIso q).hom =
    HomotopyFiberConeComparison.unitTriangle q := by
  change HomotopyFiberConeComparison.rightPresentation q
    (fibrationReplacementProjection q) (fibrationReplacementUnit q) (𝟙 Y')
    (HomotopySquareGroups.unitSquare q) = _
  rw [HomotopyFiberConeComparison.rightPresentation_canonical]
  apply Arrow.mk_injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity _ _
    (SpectrumTriangleNormalization.canonicalPost_identity_arrow q)).trans
      ((SpectrumArrow.preAt_arrow _ _ _).trans
        (SpectrumArrow.preAt_arrow _ _ (fibrationReplacement_fac q)).symm)

variable (a : X ⟶ X') (b : Y ⟶ Y')
  (γ : (mappingSpace X Y').Edge (vertexOfHom (a ≫ q)) (vertexOfHom (p ≫ b)))

lemma replacedEdge_arrow : Arrow.mk (SpectrumMappingPath.arrowHom γ) =
    Arrow.mk (SpectrumMappingPath.arrowHom (HomotopySquareGroups.replacedEdge p q a b γ)) := by
  unfold HomotopySquareGroups.replacedEdge
  exact SpectrumMappingPath.arrowHom_ofHomEq γ
    (by rw [Category.assoc, fibrationReplacement_fac]) rfl

lemma lift_pre_naturality : SpectrumMappingPath.arrowHom γ ≫
    SpectrumArrow.preAt (lift p q a b γ).map (fibrationReplacementProjection q)
      (lift p q a b γ).fac =
    SpectrumArrow.pre a q ≫ (unitRightIso q).hom := by
  apply Arrow.mk_injective
  refine (arrow_mk_comp_congr (replacedEdge_arrow p q a b γ) rfl).trans ?_
  refine (congrArg Arrow.mk (lift p q a b γ).canonicalPre_naturality).symm.trans ?_
  rw [unitRightIso_hom_triangle]
  exact (SpectrumArrow.preAt_comp_arrow a (fibrationReplacementUnit q)
    (fibrationReplacementProjection q) (fibrationReplacement_fac q) rfl).symm

lemma rightPresentation_canonical : rightPresentation p q a b γ =
    SpectrumArrow.post p b ≫ (SpectrumMappingPath.arrowIso γ).inv ≫ SpectrumArrow.pre a q := by
  have hn : (SpectrumMappingPath.arrowIso γ).hom ≫
      SpectrumArrow.preAt (lift p q a b γ).map (fibrationReplacementProjection q)
        (lift p q a b γ).fac = SpectrumArrow.pre a q ≫ (unitRightIso q).hom :=
    lift_pre_naturality p q a b γ
  have he : SpectrumArrow.preAt (lift p q a b γ).map (fibrationReplacementProjection q)
      (lift p q a b γ).fac =
      (SpectrumMappingPath.arrowIso γ).inv ≫ SpectrumArrow.pre a q ≫ (unitRightIso q).hom := by
    calc
      _ = (SpectrumMappingPath.arrowIso γ).inv ≫
          ((SpectrumMappingPath.arrowIso γ).hom ≫ SpectrumArrow.preAt
            (lift p q a b γ).map (fibrationReplacementProjection q) (lift p q a b γ).fac) := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = _ := by rw [hn]
  unfold rightPresentation
  rw [HomotopyFiberConeComparison.rightPresentation_canonical, he]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberComparison
