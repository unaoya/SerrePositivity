module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberUnitCanonical
public import SerrePositivity.KST.LocalizingInvariants.SpectrumArrowCalculus
public import SerrePositivity.KST.LocalizingInvariants.FiberMappingCanonicalPrismNaturality

/-!
概要：厳密 BF 正方形の元の模型右辺を、置換前の標準二三角形へ同定する。
方針：交差する比較と上側比較の結合律を使い、相対単位の自然性から両単位を相殺する。
規約：元の全比較のまま計算する。使われ方：指定区間を持つ模型比較の右辺表示。
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
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison

local instance canonicalSquareCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def unitTriangle := SpectrumArrow.preAt (fibrationReplacementUnit p)
  (fibrationReplacementProjection p) (fibrationReplacement_fac p)

lemma rightUnitIso_hom_triangle : (rightUnitIso p).hom = unitTriangle p := by
  apply Arrow.mk_injective
  exact (rightUnitIso_canonical p).trans
    (SpectrumArrow.preAt_arrow _ _ _).symm

lemma replacedRightPresentation_canonical : replacedRightPresentation p q a b h =
    SpectrumArrow.post (fibrationReplacementProjection p) b ≫ SpectrumArrow.preAt
      (FibrationReplacementComparison.map p q a b h) (fibrationReplacementProjection q)
      (FibrationReplacementComparison.map_projection p q a b h) := by
  apply Arrow.mk_injective
  apply arrow_mk_comp_congr
  · rfl
  · apply HomotopyArrow.congr
    unfold StrictArrow.pre
    rw [HomotopyArrow.rebase_map]
    change _ = (HomotopyArrow.rebase _ _ _).h
    rw [HomotopyArrow.rebase_map]
    rfl

lemma unitPre_arrow : Arrow.mk (SpectrumArrow.pre
    (fibrationReplacementUnit p ≫ FibrationReplacementComparison.map p q a b h)
      (fibrationReplacementProjection q)) = Arrow.mk (SpectrumArrow.pre
        (a ≫ fibrationReplacementUnit q) (fibrationReplacementProjection q)) := by
  have he := congrArg Arrow.mk
    (FibrationReplacementComparison.canonicalUnitPre_naturality p q a b h)
  exact (SpectrumArrow.preAt_arrow _ _
    (FibrationReplacementComparison.unitFirst_projection p q a b h)).symm.trans
      (he.trans (SpectrumArrow.preAt_arrow _ _
        (FibrationReplacementComparison.unitSecond_projection p q a b h)))

lemma unit_replaced_factorization :
    unitTriangle p ≫ replacedRightPresentation p q a b h =
      SpectrumArrow.post p b ≫ SpectrumArrow.preAt a q h.symm ≫ unitTriangle q := by
  rw [replacedRightPresentation_canonical, ← Category.assoc]
  unfold unitTriangle
  rw [SpectrumArrow.overlap, Category.assoc]
  apply Arrow.mk_injective
  apply arrow_mk_comp_congr rfl
  exact (SpectrumArrow.preAt_comp_arrow
    (fibrationReplacementUnit p) (FibrationReplacementComparison.map p q a b h)
    (fibrationReplacementProjection q) (FibrationReplacementComparison.map_projection p q a b h)
    _).trans ((unitPre_arrow p q a b h).trans
      (SpectrumArrow.preAt_comp_arrow a (fibrationReplacementUnit q)
        (fibrationReplacementProjection q) (fibrationReplacement_fac q) h.symm).symm)

lemma rightPresentation_canonical : rightPresentation p q a b h =
    SpectrumArrow.post p b ≫ SpectrumArrow.preAt a q h.symm := by
  unfold rightPresentation
  rw [rightUnitIso_hom_triangle, ← Category.assoc, unit_replaced_factorization,
    ← rightUnitIso_hom_triangle]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison
