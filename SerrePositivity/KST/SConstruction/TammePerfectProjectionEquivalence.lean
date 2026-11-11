module
public import SerrePositivity.KST.SConstruction.TammePerfectProjectionAxes
public import SerrePositivity.KST.LocalizingInvariants.BinaryAxesEquivalence

/-! # 元の両射影を保つ Cat^perf の Tamme 積同値
概要：同じ lax pullback の値から元の C・D の値の実積への両射影を同値にする。
方針：実分裂との合成が両軸を固定することと、全整数 π の同値検出を使う。
規約：実 BF 積と同じ射の類を保持する。使われ方：LT の正方形の頂点移送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants

variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B)
  (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete D.obj)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

include hF in
/-- 元の両射影を組にした同じ射の類は、実 Sp の同型。 -/
lemma IsPerfectLocalizingInvariant.tammePerfectProjectionHom_isIso :
    IsIso (tammePerfectProjectionHom p q hC hD F) := by
  let s := hF.tammeValueSplitComparison p q hC hD
  have hi : IsIso (s.hom ≫ tammePerfectProjectionHom p q hC hD F) := by
    apply Binary.isIso_of_axes_fixed
    · rw [← Category.assoc]
      change (SpectrumHo.hom (Binary.inl _ _) ≫
        (hF.tammeValueSplitComparison p q hC hD).hom) ≫ _ = _
      erw [hF.tammeValueSplitComparison_C]
      exact hF.tammePerfectProjectionHom_fromC p q hC hD
    · rw [← Category.assoc]
      change (SpectrumHo.hom (Binary.inr _ _) ≫
        (hF.tammeValueSplitComparison p q hC hD).hom) ≫ _ = _
      erw [hF.tammeValueSplitComparison_D]
      exact hF.tammePerfectProjectionHom_fromD p q hC hD
  have h : IsIso (s.inv ≫ (s.hom ≫ tammePerfectProjectionHom p q hC hD F)) := inferInstance
  simpa only [Iso.inv_hom_id_assoc] using h

/-- 元の二射影そのものを順方向に持つ、元の C・D の値の実積への同値。 -/
def IsPerfectLocalizingInvariant.tammePerfectProjectionEquivalence :
    SpectrumHo.obj (perfectInvariantSpectrum F (perfectLaxVertex p q hC hD)) ≅
    SpectrumHo.obj (Binary.obj
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) := by
  have := hF.tammePerfectProjectionHom_isIso p q hC hD
  exact asIso (tammePerfectProjectionHom p q hC hD F)

/-- 同じ同値の順方向は、元の二射影の値を組にした射の類そのもの。 -/
lemma IsPerfectLocalizingInvariant.tammePerfectProjectionEquivalence_hom :
    (hF.tammePerfectProjectionEquivalence p q hC hD).hom =
      tammePerfectProjectionHom p q hC hD F := rfl

/-- 同じ積同値の第一射影は、元の第一射影の値そのもの。 -/
lemma IsPerfectLocalizingInvariant.tammePerfectProjectionEquivalence_fst :
    (hF.tammePerfectProjectionEquivalence p q hC hD).hom ≫
      SpectrumHo.hom (Binary.fst
        (perfectInvariantSpectrum F (perfectStableVertex C hC))
        (perfectInvariantSpectrum F (perfectStableVertex D hD))) =
      perfectInvariantSpectrumHom F (laxFst p q)
        (perfectLaxCategory_isIdempotentComplete p q hC hD) hC :=
  tammePerfectProjectionHom_fst p q hC hD F

/-- 同じ積同値の第二射影は、元の第二射影の値そのもの。 -/
lemma IsPerfectLocalizingInvariant.tammePerfectProjectionEquivalence_snd :
    (hF.tammePerfectProjectionEquivalence p q hC hD).hom ≫
      SpectrumHo.hom (Binary.snd
        (perfectInvariantSpectrum F (perfectStableVertex C hC))
        (perfectInvariantSpectrum F (perfectStableVertex D hD))) =
      perfectInvariantSpectrumHom F (laxSnd p q)
        (perfectLaxCategory_isIdempotentComplete p q hC hD) hD :=
  tammePerfectProjectionHom_snd p q hC hD F

/-- 同じ積同値の逆の C 軸は、元の C 包含の値。 -/
lemma IsPerfectLocalizingInvariant.tammePerfectProjectionEquivalence_inv_inl :
    SpectrumHo.hom (Binary.inl
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) ≫
        (hF.tammePerfectProjectionEquivalence p q hC hD).inv =
      perfectInvariantSpectrumHom F (LaxInclusion.exactFromC p q) hC
        (perfectLaxCategory_isIdempotentComplete p q hC hD) := by
  apply (cancel_mono (hF.tammePerfectProjectionEquivalence p q hC hD).hom).mp
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (hF.tammePerfectProjectionHom_fromC p q hC hD).symm

/-- 同じ積同値の逆の D 軸は、元の D 包含の値。 -/
lemma IsPerfectLocalizingInvariant.tammePerfectProjectionEquivalence_inv_inr :
    SpectrumHo.hom (Binary.inr
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) ≫
        (hF.tammePerfectProjectionEquivalence p q hC hD).inv =
      perfectInvariantSpectrumHom F (LaxInclusion.exactFromD p q) hD
        (perfectLaxCategory_isIdempotentComplete p q hC hD) := by
  apply (cancel_mono (hF.tammePerfectProjectionEquivalence p q hC hD).hom).mp
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (hF.tammePerfectProjectionHom_fromD p q hC hD).symm

end SerrePositivity.KST.SConstruction
