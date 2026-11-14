module
public import SerrePositivity.KST.SConstruction.TammePerfectSequence

/-! # 元の Cat^perf lax pullback に対する Tamme の分裂
概要：元の lax pullback の不変量値を、元の D・C に対応する実 Sp 積へ分裂させる。
方針：証明した冪等完備性と元の半直交分解を、同じ実不変量値の積分解へ渡す。
規約：包含・切断・第一射影を元の全単体上の関手として保持する。使われ方：LT 主定理。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B)
  (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete D.obj)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 実積の左因子と、元の D の不変量値の比較。 -/
def IsPerfectLocalizingInvariant.tammeLeftFactorIso :
    perfectInvariantHoObject F (perfectStableVertex D hD) ≅ SpectrumHo.obj
      (OmegaSpectrum.homotopyFiber (NativeFiber.rightMap
        (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD)))) :=
  hF.perfectSplitLeftFactorIso (tammePerfectSequence p q hC hD)

/-- 実積の右因子と、元の C の不変量値の比較。 -/
def IsPerfectLocalizingInvariant.tammeRightFactorIso :
    perfectInvariantHoObject F (perfectStableVertex C hC) ≅ SpectrumHo.obj
      (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex
        (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD)).square 1 1)) :=
  hF.perfectSplitRightFactorIso (tammePerfectSequence p q hC hD)

/-- Tamme の分裂は、同じ元の lax pullback の値と実 Sp 積との同値。 -/
def IsPerfectLocalizingInvariant.tammeSplitEquivalence :
    SpectrumHo.obj (NativeSplit.product
      (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD))) ≅
        perfectInvariantHoObject F (perfectLaxVertex p q hC hD) :=
  hF.perfectSemiorthogonalSplitEquivalence (perfectLaxSemiorthogonal p q hC hD)

/-- 分裂の左包含は元の D からの包含の値を回収する。 -/
lemma IsPerfectLocalizingInvariant.tammeSplitEquivalence_inclusion :
    SpectrumHo.hom (Binary.inl _ _) ≫ (hF.tammeSplitEquivalence p q hC hD).hom =
      (hF.tammeLeftFactorIso p q hC hD).inv ≫
        perfectInvariantHoArrow F (LaxInclusion.exactFromD p q) hD
          (perfectLaxCategory_isIdempotentComplete p q hC hD) :=
  hF.perfectSemiorthogonalSplitEquivalence_inclusion (perfectLaxSemiorthogonal p q hC hD)

/-- 分裂の右包含は元の C からの右包含の値を回収する。 -/
lemma IsPerfectLocalizingInvariant.tammeSplitEquivalence_section :
    SpectrumHo.hom (Binary.inr _ _) ≫ (hF.tammeSplitEquivalence p q hC hD).hom =
      (hF.tammeRightFactorIso p q hC hD).inv ≫
        perfectInvariantHoArrow F (LaxInclusion.exactFromC p q) hC
          (perfectLaxCategory_isIdempotentComplete p q hC hD) :=
  hF.perfectSemiorthogonalSplitEquivalence_section (perfectLaxSemiorthogonal p q hC hD)

/-- 分裂の射影は元の lax pullback の第一射影の値を回収する。 -/
lemma IsPerfectLocalizingInvariant.tammeSplitEquivalence_projection :
    (hF.tammeSplitEquivalence p q hC hD).hom ≫
        perfectInvariantHoArrow F (laxFst p q)
          (perfectLaxCategory_isIdempotentComplete p q hC hD) hC =
      SpectrumHo.hom (Binary.snd _ _) ≫ (hF.tammeRightFactorIso p q hC hD).inv :=
  hF.perfectSemiorthogonalSplitEquivalence_projection (perfectLaxSemiorthogonal p q hC hD)

end SerrePositivity.KST.SConstruction
