module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientUniversalEdges
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientProductMap
public import SerrePositivity.KST.SConstruction.PerfectIdentityLaxValueDiagonal
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowCompositionCancellation

/-! # 元の実積比較正方形の四辺の射の類
概要：全図式の自然性と同じ四成分から、四辺を元の包含・対角・二脚の積射へ同定する。
方針：端点移送を Arrow の等号として保ち、指定した可逆成分を相殺する。
規約：整数 π の一致から射の一致を推論しない。使われ方：四辺固定の実 pullback。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
namespace PerfectLaxQuotient

private lemma perfectMovedEdgeArrow {K : Type*} [Category K]
    {OX OY NX NY A B RA RB P Q : K}
    (f : OX ⟶ OY) (g : NX ⟶ NY) (cx : OX ⟶ NX) (cy : OY ⟶ NY)
    (i : A ⟶ B) (a : RA ≅ A) (b : RB ≅ B) (u : RA ≅ P) (v : RB ≅ Q)
    (hn : f ≫ cy = cx ≫ g) (hf : Arrow.mk f = Arrow.mk i)
    (hx : Arrow.mk cx = Arrow.mk (a.inv ≫ u.hom))
    (hy : Arrow.mk cy = Arrow.mk (b.inv ≫ v.hom)) :
    Arrow.mk g = Arrow.mk (u.inv ≫ (a.hom ≫ i ≫ b.inv) ≫ v.hom) := by
  have he : (a.inv ≫ u.hom) ≫ (u.inv ≫ (a.hom ≫ i ≫ b.inv) ≫ v.hom) =
      i ≫ (b.inv ≫ v.hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  have hfg := (congrArg Arrow.mk hn).symm.trans (arrow_mk_comp_congr hf hy)
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_cancel_comp_left hx (hfg.trans (congrArg Arrow.mk he.symm))

private lemma perfectMovedEdgeLeftId {K : Type*} [Category K]
    {OX OY NX NY A B RA RB Q : K}
    (f : OX ⟶ OY) (g : NX ⟶ NY) (cx : OX ⟶ NX) (cy : OY ⟶ NY)
    (i : A ⟶ B) (a : RA ≅ A) (b : RB ≅ B) (v : RB ≅ Q)
    (hn : f ≫ cy = cx ≫ g) (hf : Arrow.mk f = Arrow.mk i)
    (hx : Arrow.mk cx = Arrow.mk a.inv)
    (hy : Arrow.mk cy = Arrow.mk (b.inv ≫ v.hom)) :
    Arrow.mk g = Arrow.mk ((a.hom ≫ i ≫ b.inv) ≫ v.hom) := by
  have h := perfectMovedEdgeArrow f g cx cy i a b (Iso.refl RA) v hn hf
    (by simpa only [Iso.refl_hom, Category.comp_id] using hx) hy
  simpa only [Iso.refl_inv, Category.id_comp] using h

private lemma perfectMovedEdgeBothId {K : Type*} [Category K]
    {OX OY NX NY A B RA RB : K}
    (f : OX ⟶ OY) (g : NX ⟶ NY) (cx : OX ⟶ NX) (cy : OY ⟶ NY)
    (i : A ⟶ B) (a : RA ≅ A) (b : RB ≅ B)
    (hn : f ≫ cy = cx ≫ g) (hf : Arrow.mk f = Arrow.mk i)
    (hx : Arrow.mk cx = Arrow.mk a.inv) (hy : Arrow.mk cy = Arrow.mk b.inv) :
    Arrow.mk g = Arrow.mk (a.hom ≫ i ≫ b.inv) := by
  have h := perfectMovedEdgeLeftId f g cx cy i a b (Iso.refl RB) hn hf hx
    (by simpa only [Iso.refl_hom, Category.comp_id] using hy)
  simpa only [Iso.refl_hom, Category.comp_id] using h

private lemma perfectCancelIsoLeft {K : Type*} [Category K]
    {X Y Z : K} (e : X ≅ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : f = e.hom ≫ g) : e.inv ≫ f = g := by
  rw [h, Iso.inv_hom_id_assoc]

variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 同じ全図式を移した bottom 辺は、元の指定された値の射の類。 -/
lemma productSquare_bottom_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (d.productSquare hF)) =
    Arrow.mk (perfectInvariantSpectrumHom F d.inclusion
      d.left_complete d.middle_complete ≫ (hF.tammePerfectProjectionEquivalence p q
        d.c_complete d.d_complete).hom) := by
  have h := perfectMovedEdgeLeftId
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (d.universalValueSquare F)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (d.productSquare hF))
    (d.productComponent hF 0 0) (d.productComponent hF 1 0)
    (perfectInvariantHoArrow F d.inclusion
      d.left_complete d.middle_complete)
    (perfectInvariantSpectrumIso F (perfectStableVertex d.left d.left_complete))
      (perfectInvariantSpectrumIso F (perfectLaxVertex p q d.c_complete d.d_complete))
    (hF.tammePerfectProjectionEquivalence p q d.c_complete d.d_complete)
    (d.productSquare_bottom_naturality hF) (d.universalValueSquare_bottom_arrow F)
    (d.productComponent00_arrow hF)
    (d.productComponent10_arrow hF)
  exact h

/-- 同じ全図式を移した left 辺は、元の指定された値の射の類。 -/
lemma productSquare_left_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoLeft (d.productSquare hF)) =
    Arrow.mk (perfectInvariantSpectrumHom F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q d.inclusion
      d.sequence.projection)
      d.left_complete d.sequence.right_complete) := by
  have h := perfectMovedEdgeBothId
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoLeft (d.universalValueSquare F)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoLeft (d.productSquare hF))
    (d.productComponent hF 0 0) (d.productComponent hF 0 1)
    (perfectInvariantHoArrow F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q d.inclusion
      d.sequence.projection)
      d.left_complete d.sequence.right_complete)
    (perfectInvariantSpectrumIso F (perfectStableVertex d.left d.left_complete))
      (perfectInvariantSpectrumIso F d.sequence.rightVertex)
    (d.productSquare_left_naturality hF) (d.universalValueSquare_left_arrow F)
    (d.productComponent00_arrow hF)
    (d.productComponent01_arrow hF)
  exact h

/-- 同じ全図式を移した top 辺は、元の指定された値の射の類。 -/
lemma productSquare_top_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (d.productSquare hF)) =
    Arrow.mk (SpectrumHo.hom (Binary.lift
      (𝟙 (perfectInvariantSpectrum F d.sequence.rightVertex))
      (𝟙 (perfectInvariantSpectrum F d.sequence.rightVertex)))) := by
  have h := perfectMovedEdgeLeftId
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (d.universalValueSquare F)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (d.productSquare hF))
    (d.productComponent hF 0 1) (d.productComponent hF 1 1)
    (perfectInvariantHoArrow F (IdentityLax.exactDiagonal d.sequence.right)
      d.sequence.right_complete (perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right)
        (𝟙 d.sequence.right)
      d.sequence.right_complete d.sequence.right_complete))
    (perfectInvariantSpectrumIso F d.sequence.rightVertex) (perfectInvariantSpectrumIso F
      (perfectLaxVertex (𝟙 d.sequence.right) (𝟙 d.sequence.right)
      d.sequence.right_complete d.sequence.right_complete))
    (hF.tammePerfectProjectionEquivalence (𝟙 d.sequence.right) (𝟙 d.sequence.right)
      d.sequence.right_complete d.sequence.right_complete)
    (d.productSquare_top_naturality hF) (d.universalValueSquare_top_arrow F)
    (d.productComponent01_arrow hF)
    (d.productComponent11_arrow hF)
  have he := congrArg Arrow.mk
    (hF.perfectIdentityLaxValueDiagonal_product d.sequence.right d.sequence.right_complete)
  exact h.trans he

/-- 同じ全図式を移した right 辺は、元の指定された値の射の類。 -/
lemma productSquare_right_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (d.productSquare hF)) =
    Arrow.mk (SpectrumHo.hom (d.productLegMap F)) := by
  have h := perfectMovedEdgeArrow
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (d.universalValueSquare F)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (d.productSquare hF))
    (d.productComponent hF 1 0) (d.productComponent hF 1 1)
    (perfectInvariantHoArrow F (LaxUniversalDifference.exactLift p q d.sequence.projection)
      d.middle_complete (perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right) (𝟙
        d.sequence.right)
      d.sequence.right_complete d.sequence.right_complete))
    (perfectInvariantSpectrumIso F (perfectLaxVertex p q d.c_complete d.d_complete))
      (perfectInvariantSpectrumIso F (perfectLaxVertex (𝟙 d.sequence.right) (𝟙 d.sequence.right)
      d.sequence.right_complete d.sequence.right_complete))
    (hF.tammePerfectProjectionEquivalence p q d.c_complete d.d_complete)
      (hF.tammePerfectProjectionEquivalence (𝟙 d.sequence.right) (𝟙 d.sequence.right)
      d.sequence.right_complete d.sequence.right_complete)
    (d.productSquare_right_naturality hF) (d.universalValueSquare_right_arrow F)
    (d.productComponent10_arrow hF)
    (d.productComponent11_arrow hF)
  exact h.trans (congrArg Arrow.mk (perfectCancelIsoLeft (hF.tammePerfectProjectionEquivalence
    p q d.c_complete d.d_complete)
    _ _ (d.product_projection_comm hF)))

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
