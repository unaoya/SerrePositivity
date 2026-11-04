module

public import SerrePositivity.KST.LocalizingInvariants.LaxSemiorthogonal
public import SerrePositivity.KST.LocalizingInvariants.SemiorthogonalInvariant
public import SerrePositivity.KST.LocalizingInvariants.SpectrumProductAxes

/-!
概要：Tamme の lax pullback の値を、元の C・D の値の実 Sp 積へ分裂する。
方針：K-5 の splitEquivalence の二因子を元の値に同定し、C,D の順に交換する。
規約：Sp の安定性は仮定しない。使われ方：K-8 の抽象 Tamme 定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant

variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

def tammeFactorComparison : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ≅
    SpectrumHo.obj (NativeSplit.product (hΦ.abstractFiberTriangle (laxVerdierSequence p q))) :=
  Binary.mapIso (hΦ.splitRightFactorIso (laxVerdierSequence p q))
    (hΦ.splitLeftFactorIso (laxVerdierSequence p q)) ≪≫ Binary.swapIso _ _

/-- 元の値 E(C)×E(D) の実 ∞ 積から E(lax pullback) への同値。 -/
def tammeSplitComparison : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ≅
    SpectrumHo.obj (value Φ (laxCategory p q)) :=
  hΦ.tammeFactorComparison p q ≪≫ hΦ.semiorthogonalSplitEquivalence (laxSemiorthogonal p q)

/-- 要求された向きの Sp 同値。因子の順は C,D。 -/
def tammeSplitEquivalence : SpectrumHo.obj (value Φ (laxCategory p q)) ≅
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) := (hΦ.tammeSplitComparison p q).symm

/-- 積因子は元の値であり、積は実際の ∞ 極限錐。 -/
def tammeProductCone (Φ : StableInfinity.{u} ⟶ Sp.{u}) (C D : StableCategory.{u}) :=
  spectrumBinaryProductInfinityCone (value Φ C) (value Φ D)

lemma tammeProductCone_isLimit : IsLimitCone (tammeProductCone Φ C D) :=
  spectrumBinaryProductInfinityCone_isLimit _ _

lemma tammeFactorComparison_inl : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    (hΦ.tammeFactorComparison p q).hom =
      (hΦ.splitRightFactorIso (laxVerdierSequence p q)).hom ≫ SpectrumHo.hom (Binary.inr _ _) := by
  change SpectrumHo.hom (Binary.inl _ _) ≫ (Binary.hoMap _ _ ≫ (Binary.swapIso _ _).hom) = _
  rw [← Category.assoc, Binary.hoMap_inl, Category.assoc, Binary.swapIso_inl]

lemma tammeFactorComparison_inr : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    (hΦ.tammeFactorComparison p q).hom =
      (hΦ.splitLeftFactorIso (laxVerdierSequence p q)).hom ≫ SpectrumHo.hom (Binary.inl _ _) := by
  change SpectrumHo.hom (Binary.inr _ _) ≫ (Binary.hoMap _ _ ≫ (Binary.swapIso _ _).hom) = _
  rw [← Category.assoc, Binary.hoMap_inr, Category.assoc, Binary.swapIso_inr]

lemma tammeSplitComparison_C : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    (hΦ.tammeSplitComparison p q).hom =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) := by
  change SpectrumHo.hom (Binary.inl _ _) ≫ ((hΦ.tammeFactorComparison p q).hom ≫
    (hΦ.semiorthogonalSplitEquivalence (laxSemiorthogonal p q)).hom) = _
  rw [← Category.assoc, tammeFactorComparison_inl, Category.assoc]
  erw [hΦ.semiorthogonalSplitEquivalence_section (laxSemiorthogonal p q),
    Iso.hom_inv_id_assoc]
  rfl

lemma tammeSplitComparison_D : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    (hΦ.tammeSplitComparison p q).hom =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) := by
  change SpectrumHo.hom (Binary.inr _ _) ≫ ((hΦ.tammeFactorComparison p q).hom ≫
    (hΦ.semiorthogonalSplitEquivalence (laxSemiorthogonal p q)).hom) = _
  rw [← Category.assoc, tammeFactorComparison_inr, Category.assoc]
  erw [hΦ.semiorthogonalSplitEquivalence_inclusion (laxSemiorthogonal p q),
    Iso.hom_inv_id_assoc]
  rfl

lemma tammeSplitComparison_projection : (hΦ.tammeSplitComparison p q).hom ≫
    SpectrumHo.hom (valueMap Φ (laxFst p q)) =
      SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) := by
  change ((hΦ.tammeFactorComparison p q).hom ≫
    (hΦ.semiorthogonalSplitEquivalence (laxSemiorthogonal p q)).hom) ≫ _ = _
  rw [Category.assoc]
  erw [hΦ.semiorthogonalSplitEquivalence_projection (laxSemiorthogonal p q)]
  rw [← Category.assoc]
  change ((Binary.mapIso (hΦ.splitRightFactorIso (laxVerdierSequence p q))
    (hΦ.splitLeftFactorIso (laxVerdierSequence p q)) ≪≫ Binary.swapIso _ _).hom ≫
    SpectrumHo.hom (Binary.snd _ _)) ≫ _ = _
  erw [Binary.mapIso_swap_snd (hΦ.splitRightFactorIso (laxVerdierSequence p q))
    (hΦ.splitLeftFactorIso (laxVerdierSequence p q))]
  rw [Category.assoc]
  erw [Iso.hom_inv_id]
  exact Category.comp_id _

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
