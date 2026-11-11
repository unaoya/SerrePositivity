module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

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

open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant

variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

def tammeFactorComparison : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ≅
    SpectrumHo.obj (NativeSplit.product (hΦ.abstractFiberTriangle (laxVerdierSequence p q))) :=
  Binary.mapIso (hΦ.splitRightFactorIso (laxVerdierSequence p q))
    (hΦ.splitLeftFactorIso (laxVerdierSequence p q)) ≪≫ Binary.swapIso _ _

/-- 元の値 E(C)×E(D) の実 ∞ 積から E(lax pullback) への同値。 -/
def tammeSplitComparison : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ≅
    SpectrumHo.obj (value Φ (laxCategory p q)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison hΦ) p q ≪≫ hΦ.semiorthogonalSplitEquivalence (laxSemiorthogonal p q)

/-- 要求された向きの Sp 同値。因子の順は C,D。 -/
def tammeSplitEquivalence : SpectrumHo.obj (value Φ (laxCategory p q)) ≅
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).symm

/-- 積因子は元の値であり、積は実際の ∞ 極限錐。 -/
def tammeProductCone (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductInfinityCone (value Φ C) (value Φ D)

lemma tammeProductCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeProductCone Φ C D) :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductInfinityCone_isLimit _ _

lemma tammeFactorComparison_inl : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison hΦ) p q).hom =
      (hΦ.splitRightFactorIso (laxVerdierSequence p q)).hom ≫ SpectrumHo.hom (Binary.inr _ _) := by
  change SpectrumHo.hom (Binary.inl _ _) ≫ (Binary.hoMap _ _ ≫ (Binary.swapIso _ _).hom) = _
  rw [← Category.assoc, Binary.hoMap_inl, Category.assoc, Binary.swapIso_inl]

lemma tammeFactorComparison_inr : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison hΦ) p q).hom =
      (hΦ.splitLeftFactorIso (laxVerdierSequence p q)).hom ≫ SpectrumHo.hom (Binary.inl _ _) := by
  change SpectrumHo.hom (Binary.inr _ _) ≫ (Binary.hoMap _ _ ≫ (Binary.swapIso _ _).hom) = _
  rw [← Category.assoc, Binary.hoMap_inr, Category.assoc, Binary.swapIso_inr]

lemma tammeSplitComparison_C : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).hom =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) := by
  change SpectrumHo.hom (Binary.inl _ _) ≫ (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison hΦ) p q).hom ≫
    (hΦ.semiorthogonalSplitEquivalence (laxSemiorthogonal p q)).hom) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison_inl, Category.assoc]
  erw [hΦ.semiorthogonalSplitEquivalence_section (laxSemiorthogonal p q),
    Iso.hom_inv_id_assoc]
  rfl

lemma tammeSplitComparison_D : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).hom =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) := by
  change SpectrumHo.hom (Binary.inr _ _) ≫ (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison hΦ) p q).hom ≫
    (hΦ.semiorthogonalSplitEquivalence (laxSemiorthogonal p q)).hom) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison_inr, Category.assoc]
  erw [hΦ.semiorthogonalSplitEquivalence_inclusion (laxSemiorthogonal p q),
    Iso.hom_inv_id_assoc]
  rfl

lemma tammeSplitComparison_projection : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).hom ≫
    SpectrumHo.hom (valueMap Φ (laxFst p q)) =
      SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) := by
  change (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison hΦ) p q).hom ≫
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

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFactorComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFactorComparison_inl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison_inl

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFactorComparison_inr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison_inr

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeProductCone (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeProductCone := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeProductCone

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeProductCone_isLimit := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeProductCone_isLimit

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeSplitComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeSplitComparison_C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_C

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeSplitComparison_D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_D

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeSplitComparison_projection := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_projection

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitEquivalence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeSplitEquivalence := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFactorComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFactorComparison._proof_1
