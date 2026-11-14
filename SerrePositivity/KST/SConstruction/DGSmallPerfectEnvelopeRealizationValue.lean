module
public import SerrePositivity.KST.SConstruction.DGPerfectRealizationPerfectYoneda
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.NativePerfectYonedaEquivalence
public import SerrePositivity.KST.SConstruction.FunctorIsoEquivalenceReflection

/-!
概要：指定小 Perf 包絡の実 realization を、元の固定 ν 包絡値同値へ全比較する。
方針：同じ元 Yoneda の全同値で前合成し、元代表評価と包絡評価を照合して反映する。
規約：元包絡・指定実包含・元 tensor 評価を保持し、別の値同値を選ばない。
使われ方：実逆回転の二段評価を元 resolved 商への指定終域比較へ接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type (u + 1)) [DGCategory R D] [Small.{u} D]
  (J : Type (u + 1)) [Small.{u} J] (X : J → PerfectDGModule R D)
local notation "C" => DGSmallPerfectEnvelope R D J X
local notation "I" => dgSmallPerfectEnvelopeInclusion R D J X
local notation "VP" => dgPerfectRealizationPerfect R (C) D (I)

/-- 概要：元小包絡の同じ strict Perf realization と指定 ν 値同値は全自然に比較される。
方針：元 Yoneda 同値の前で元代表評価と保存済み包絡評価を貼り、同じ同値で反映する。
規約：元の全評価同型を保持。使われ方：二段実評価と固定 ν 終域の全接続。 -/
def dgSmallPerfectEnvelopeRealizationValueComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKNativePerfectValueEquivalence R (C)).hom ≫
      (dgSmallPerfectEnvelopeValueEquivalence R D J X).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP) ≫ (dgKNativePerfectValueEquivalence R D).hom) := by
  let eY := @_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePerfectYonedaEquivalence R _ (C) _ _
    (dgSmallPerfectEnvelope_pretriangulated R D J X)
    (dgSmallPerfectEnvelope_complete R D J X)
  let s := (dgSmallPerfectEnvelopeValueEquivalence R D J X).hom
  let v := (dgKNativePerfectValueEquivalence R D).hom
  have hC := @dgKNativeValueComparison_eq R _ (C) _ _
    (dgSmallPerfectEnvelope_pretriangulated R D J X)
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (eY.hom ≫ (dgKNativePerfectValueEquivalence R (C)).hom ≫ s)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) ≫ v) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgSmallPerfectEnvelopeValueEquivalence_native R D J X)
      ((congrArg (fun F => F ≫ s) hC).trans (Category.assoc _ _ _)) rfl
  have hright : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eY.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP) ≫ v)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) ≫ v) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      ((dgPerfectRealizationPerfectYonedaComparison R (C) D (I)).postcomp v)
      (Category.assoc _ _ _) rfl
  exact functorIsoReflectPreEquivalence eY (hleft.trans hright.symm)

end SerrePositivity.KST.SConstruction
