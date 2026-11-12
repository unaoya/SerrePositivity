module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeRealizationValue
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationRealizedFactorization
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisBaseValue
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisInverseRotationPerfectRealized

/-!
概要：元実差の指定 ν 終域評価を、同じ二段 strict Perf realization へ全比較する。
方針：元実像評価の回収に二段の包絡 realization 比較を合成する。
規約：保存済みの元終域同値を保持し、残終端から別の評価を定義しない。
使われ方：共通実長方形の外周商辺と元 resolved 射影の全比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "P" => DGCategoryCellResolution.Source R (B)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "F" => dgOdotMilnorRightAxisQuotientSource R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d
local notation "T" => DGPerfectComparisonBase R (Q) (F) (G)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "LT" => DGIdentityHomGluing R (T)
local notation "LU" => DGIdentityHomGluing R (U)
local notation "X" => dgPerfectComparisonFamily R (Q) (F) (G)
local notation "Z" => dgHomGluingLoopConeFamily R (T) (T) (T)
  (DGFunctor.id (T)) (DGFunctor.id (T))
local notation "Cn" => dgHomGluingConeFunctor R (U) (U) (U)
  (DGFunctor.id (U)) (DGFunctor.id (U))
local notation "iD" => dgSmallPerfectEnvelopeInclusion R (U) (LU) (EnrichedFunctor.obj (Cn))
local notation "J1" => dgSmallPerfectEnvelopeInclusion R (T) ((LT) ⊕ (LT)) (Z)
local notation "J2" => dgSmallPerfectEnvelopeInclusion R (Q) ((P) ⊕ (P)) (X)
local notation "VP1" => dgPerfectRealizationPerfect R (U) (T) (J1)
local notation "VP2" => dgPerfectRealizationPerfect R (T) (Q) (J2)
local notation "eD" => dgOdotMilnorRightAxisIdentityDifferenceNativeValueEquivalence R d
local notation "eT" => dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence R d

/-- 概要：元実差の指定終域値は同じ二段実 realization の評価と全比較される。
方針：元全像回収と二段の元包絡値比較をそのまま貼る。
規約：元指定評価を変更しない。使われ方：実合成辺を保存済み二段全比較へ渡す。 -/
def dgOdotMilnorRightAxisDifferenceRealizationNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((eD).hom ≫ (eT).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (iD) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP2) ≫
      (dgKNativePerfectValueEquivalence R (Q)).hom) := by
  let vU := (dgKNativePerfectValueEquivalence R (U)).hom
  let vT := (dgKNativePerfectValueEquivalence R (T)).hom
  let vQ := (dgKNativePerfectValueEquivalence R (Q)).hom
  let s1 := (dgOdotMilnorRightAxisBaseStepValueEquivalence R d).hom
  let s2 := (dgOdotMilnorRightAxisComparisonBaseValueEquivalence R d).hom
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (iD)
  let r1 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP1)
  let r2 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP2)
  have h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((eD).hom ≫ (eT).hom) (p ≫ vU ≫ s1 ≫ s2) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      ((dgOdotMilnorRightAxisIdentityDifferenceValueEquivalence_native R d).postcomp
        (dgOdotMilnorRightAxisBaseValueEquivalence R d).hom)
      (Category.assoc _ _ _) (Category.assoc _ _ _)
  have h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p ≫ vU ≫ s1 ≫ s2) (p ≫ r1 ≫ vT ≫ s2) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
        ((dgSmallPerfectEnvelopeRealizationValueComparison R (T) ((LT) ⊕ (LT)) (Z)).postcomp s2)
        (Category.assoc _ _ _) (Category.assoc _ _ _)) p
  have h2 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p ≫ r1 ≫ vT ≫ s2) (p ≫ r1 ≫ r2 ≫ vQ) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgSmallPerfectEnvelopeRealizationValueComparison R (Q) ((P) ⊕ (P)) (X))
        (p ≫ r1)) (Category.assoc _ _ _) (Category.assoc _ _ _)
  exact h0.trans (h1.trans h2)

end SerrePositivity.KST.SConstruction
