module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.Modules.FreeHammockCoefficientNerve
public import SerrePositivity.EInfinity.SimplicialLocalization.LocalizationNerveSource
public import SerrePositivity.EInfinity.SimplicialLocalization.RelativeHammockSourceComparison

/-!
# 同じ局所化の源の写像の全係数自然性

概要：Dwyer–Kan §9 の左右比較を同じ係数関手について貼り合わせる。
方針：元の全 nerve の可換正方形を augmentation の同値で移す。
規約：源の写像の既存の逆の選択を保ち、全関手間の比較を与える。
使われ方：HA §4.2.3 の BE 加群族の同じ指定局所化辺との照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.EInfinity SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable {C D : RelativeCategory.{u}} (F : C ⟶ D)

/-- 概要：同じ hammock・自由局所化の比較は全係数関手に自然（Dwyer–Kan §9）。
方針：元の二つの正方形と同じ augmentation の可逆比較を貼り合わせる。
規約：元の既存の模型比較。使われ方：同じ局所化の源の自然性。 -/
def kanHammockLocalizationCoefficientIso :
    FunctorIso (relativeKanHammockNerve F ≫ (kanHammockLocalizationEquivalence D).hom)
      ((kanHammockLocalizationEquivalence C).hom ≫ localizationNerveMap F) := by
  let a := (kanFreeHammockAugmentationNerve_equivalence C).choose
  let f := relativeKanHammockNerve F ≫ (kanHammockLocalizationEquivalence D).hom
  let g := (kanHammockLocalizationEquivalence C).hom ≫ localizationNerveMap F
  have hD := (kanHammockLocalizationComparison D).precomp (kanFreeHammockCoefficientNerve F)
  rw [← Category.assoc, kanFreeHammockCoefficientNerve_augmentation,
    Category.assoc, kanFreeHammockCoefficientNerve_comparison] at hD
  have hC := (kanHammockLocalizationComparison C).postcomp (localizationNerveMap F)
  have hC' : FunctorIso (a.hom ≫ g)
      (kanFreeHammockComparisonNerve C ≫ localizationNerveMap F) := by
    change FunctorIso
      (kanFreeHammockAugmentationNerve C ≫
        ((kanHammockLocalizationEquivalence C).hom ≫ localizationNerveMap F))
      (kanFreeHammockComparisonNerve C ≫ localizationNerveMap F)
    simpa only [Category.assoc] using hC
  have h : FunctorIso (a.hom ≫ f) (a.hom ≫ g) := hD ≪≫ hC'.symm
  have h' := h.precomp a.inv
  have hl := a.invHomIso.postcomp f
  have hr := a.invHomIso.postcomp g
  have hl' : FunctorIso f (a.inv ≫ (a.hom ≫ f)) := by
    simpa only [Category.assoc, Category.id_comp] using hl.symm
  have hr' : FunctorIso (a.inv ≫ (a.hom ≫ g)) g := by
    simpa only [Category.assoc, Category.id_comp] using hr
  exact hl' ≪≫ h' ≪≫ hr'

/-- 概要：同じ局所化の源の写像は元の係数関手に全関手間で自然（Dwyer–Kan §9）。
方針：元の hammock 側の厳密な自然性と同じ模型比較の自然性を貼る。
規約：源の写像を選び直さない。使われ方：指定弱辺の比較の入口。 -/
def localizationNerveSourceNaturalityIso :
    FunctorIso (localizationNerveSourceMap C ≫ localizationNerveMap F)
      (nerveMap F.functor ≫ localizationNerveSourceMap D) := by
  have h := (kanHammockLocalizationCoefficientIso F).precomp (hammockLocalizationNerveMap C)
  rw [← Category.assoc, relativeKanHammockNerve_source, Category.assoc] at h
  simpa only [localizationNerveSourceMap, Category.assoc] using h.symm

attribute [cite HTT "1.2.7" (partial := component) "同じ相対局所化の係数関手について、関手準圏のホモトピー圏での可逆比較を構成する部分。任意の関手圏の存在や局所化の普遍性は主張しない。"] kanHammockLocalizationCoefficientIso
attribute [cite HTT "1.2.7" (partial := component) "同じ相対局所化の係数関手について、関手準圏のホモトピー圏での可逆比較を構成する部分。任意の関手圏の存在や局所化の普遍性は主張しない。"] localizationNerveSourceNaturalityIso

end SerrePositivity.EInfinity.Modules
