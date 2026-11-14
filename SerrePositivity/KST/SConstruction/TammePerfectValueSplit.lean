module
public import SerrePositivity.KST.SConstruction.PerfectInvariantSpectrum
public import SerrePositivity.KST.SConstruction.TammePerfectSplit
public import SerrePositivity.KST.LocalizingInvariants.SpectrumProductAxes

/-! # 元の C・D の不変量値の BF 積による Tamme 分裂
概要：既存の実分裂の二因子を元の値の BF 表示に同定し、C・D の順へ移す。
方針：同じ値の spectrumIso と実積の因子比較を使い、元の両包含を回収する。
規約：全整数群の積で代用しない。使われ方：元の両射影を持つ積同値の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants

private lemma tammeFactorLeftAxis {A B X Y : OmegaSpectrum.{u}}
    (e : SpectrumHo.obj A ≅ SpectrumHo.obj X) (d : SpectrumHo.obj B ≅ SpectrumHo.obj Y) :
    SpectrumHo.hom (Binary.inl A B) ≫ (Binary.mapIso e d ≪≫ Binary.swapIso X Y).hom =
      e.hom ≫ SpectrumHo.hom (Binary.inr Y X) := by
  change SpectrumHo.hom (Binary.inl A B) ≫
    (Binary.hoMap e.hom d.hom ≫ (Binary.swapIso X Y).hom) = _
  rw [← Category.assoc, Binary.hoMap_inl, Category.assoc, Binary.swapIso_inl]

private lemma tammeFactorRightAxis {A B X Y : OmegaSpectrum.{u}}
    (e : SpectrumHo.obj A ≅ SpectrumHo.obj X) (d : SpectrumHo.obj B ≅ SpectrumHo.obj Y) :
    SpectrumHo.hom (Binary.inr A B) ≫ (Binary.mapIso e d ≪≫ Binary.swapIso X Y).hom =
      d.hom ≫ SpectrumHo.hom (Binary.inl Y X) := by
  change SpectrumHo.hom (Binary.inr A B) ≫
    (Binary.hoMap e.hom d.hom ≫ (Binary.swapIso X Y).hom) = _
  rw [← Category.assoc, Binary.hoMap_inr, Category.assoc, Binary.swapIso_inr]

private lemma tammeTransportedSplitAxis {K : Type*} [Category K]
    {P A X Y M T : K} (f : A ⟶ P) (c : P ⟶ Y) (n : A ≅ X) (e : X ≅ T)
    (a : T ⟶ Y) (s : Y ⟶ M) (i : X ⟶ M) (Z : K) (t : M ⟶ Z)
    (hf : f ≫ c = n.hom ≫ e.hom ≫ a) (hs : a ≫ s = e.inv ≫ i) :
    f ≫ (c ≫ s ≫ t) = n.hom ≫ i ≫ t := by
  calc
    f ≫ (c ≫ s ≫ t) = (f ≫ c) ≫ s ≫ t := by simp only [Category.assoc]
    _ = (n.hom ≫ e.hom ≫ a) ≫ s ≫ t := by rw [hf]
    _ = n.hom ≫ e.hom ≫ (a ≫ s) ≫ t := by simp only [Category.assoc]
    _ = n.hom ≫ e.hom ≫ (e.inv ≫ i) ≫ t := by rw [hs]
    _ = n.hom ≫ i ≫ t := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B)
  (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete D.obj)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 元の C・D の値から、元の分裂の二因子への実積同値。 -/
def IsPerfectLocalizingInvariant.tammeValueFactorComparison :
    SpectrumHo.obj (Binary.obj
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) ≅
    SpectrumHo.obj (NativeSplit.product
      (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD))) :=
  Binary.mapIso
    (perfectInvariantSpectrumIso F (perfectStableVertex C hC) ≪≫
      hF.tammeRightFactorIso p q hC hD)
    (perfectInvariantSpectrumIso F (perfectStableVertex D hD) ≪≫
      hF.tammeLeftFactorIso p q hC hD) ≪≫ Binary.swapIso _ _

/-- 元の C・D の値の実積から、同じ lax pullback の値の BF 表示への同値。 -/
def IsPerfectLocalizingInvariant.tammeValueSplitComparison :
    SpectrumHo.obj (Binary.obj
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) ≅
    SpectrumHo.obj (perfectInvariantSpectrum F (perfectLaxVertex p q hC hD)) :=
  hF.tammeValueFactorComparison p q hC hD ≪≫ hF.tammeSplitEquivalence p q hC hD ≪≫
    (perfectInvariantSpectrumIso F (perfectLaxVertex p q hC hD)).symm

/-- 実積の C 軸の因子比較は、元の C 値の比較と元の右軸。 -/
lemma IsPerfectLocalizingInvariant.tammeValueFactorComparison_inl :
    SpectrumHo.hom (Binary.inl
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) ≫
        (hF.tammeValueFactorComparison p q hC hD).hom =
      (perfectInvariantSpectrumIso F (perfectStableVertex C hC)).hom ≫
        (hF.tammeRightFactorIso p q hC hD).hom ≫ SpectrumHo.hom (Binary.inr
          (OmegaSpectrum.homotopyFiber (NativeFiber.rightMap
            (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD))))
          (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex
            (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD)).square 1 1))) := by
  exact (tammeFactorLeftAxis
    (perfectInvariantSpectrumIso F (perfectStableVertex C hC) ≪≫
      hF.tammeRightFactorIso p q hC hD)
    (perfectInvariantSpectrumIso F (perfectStableVertex D hD) ≪≫
      hF.tammeLeftFactorIso p q hC hD)).trans (Category.assoc _ _ _)

/-- 実積の D 軸の因子比較は、元の D 値の比較と元の左軸。 -/
lemma IsPerfectLocalizingInvariant.tammeValueFactorComparison_inr :
    SpectrumHo.hom (Binary.inr
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) ≫
        (hF.tammeValueFactorComparison p q hC hD).hom =
      (perfectInvariantSpectrumIso F (perfectStableVertex D hD)).hom ≫
        (hF.tammeLeftFactorIso p q hC hD).hom ≫ SpectrumHo.hom (Binary.inl
          (OmegaSpectrum.homotopyFiber (NativeFiber.rightMap
            (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD))))
          (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex
            (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD)).square 1 1))) := by
  exact (tammeFactorRightAxis
    (perfectInvariantSpectrumIso F (perfectStableVertex C hC) ≪≫
      hF.tammeRightFactorIso p q hC hD)
    (perfectInvariantSpectrumIso F (perfectStableVertex D hD) ≪≫
      hF.tammeLeftFactorIso p q hC hD)).trans (Category.assoc _ _ _)

/-- 同じ実積分裂の C 軸は、元の C 包含の値の同じ射の類。 -/
lemma IsPerfectLocalizingInvariant.tammeValueSplitComparison_C :
    SpectrumHo.hom (Binary.inl
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) ≫
        (hF.tammeValueSplitComparison p q hC hD).hom =
      perfectInvariantSpectrumHom F (LaxInclusion.exactFromC p q) hC
        (perfectLaxCategory_isIdempotentComplete p q hC hD) :=
  tammeTransportedSplitAxis _ _ _ _ _ _ _ _ _
    (hF.tammeValueFactorComparison_inl p q hC hD)
    (hF.tammeSplitEquivalence_section p q hC hD)

/-- 同じ実積分裂の D 軸は、元の D 包含の値の同じ射の類。 -/
lemma IsPerfectLocalizingInvariant.tammeValueSplitComparison_D :
    SpectrumHo.hom (Binary.inr
      (perfectInvariantSpectrum F (perfectStableVertex C hC))
      (perfectInvariantSpectrum F (perfectStableVertex D hD))) ≫
        (hF.tammeValueSplitComparison p q hC hD).hom =
      perfectInvariantSpectrumHom F (LaxInclusion.exactFromD p q) hD
        (perfectLaxCategory_isIdempotentComplete p q hC hD) :=
  tammeTransportedSplitAxis _ _ _ _ _ _ _ _ _
    (hF.tammeValueFactorComparison_inr p q hC hD)
    (hF.tammeSplitEquivalence_inclusion p q hC hD)

end SerrePositivity.KST.SConstruction
