module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeValue
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeFunctorLift
public import SerrePositivity.KST.SConstruction.DGKNativeNuNaturality

/-!
概要：指定実像小模型への元の厳密持ち上げの ν 辺を、元 Perf 関手全体へ比較する。
方針：同じ持ち上げの native／ν 自然性、包絡値評価、全 dg 包含回収を貼る。
規約：元関手を共役で置換しない。全 Hom を保持する。
使われ方：実中央射の二像成分と元 graph Perf 延長の固定 ν 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type (u + 1)) [DGCategory R D] [Small.{u} D]
  (J : Type (u + 1)) [Small.{u} J] (X : J → PerfectDGModule R D)
  (P : Type (u + 1)) [DGCategory R P] [Small.{u} P] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R P]
  (F : DGFunctor R P (PerfectDGModule R D)) (i : P → J) (h : ∀ a, X (i a) = F.obj a)
local notation "C" => DGSmallPerfectEnvelope R D J X
local notation "L" => dgSmallPerfectEnvelopeFunctorLift R D J X F i h

/-- 概要：同じ持ち上げの ν 辺と元 Perf 関手の全比較。
方針：同じ native 自然性と全像評価を合成し、元 dg 包含等号で回収する。
規約：元の対象と全 Hom 作用を保持。使われ方：固定 ν 上の実二成分比較。 -/
def dgSmallPerfectEnvelopeLiftNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R P ≫
      (dgKNativeInputExactMap R P (C) (L)).hom ≫
      (dgSmallPerfectEnvelopeValueEquivalence R D J X).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ (dgKNativePerfectValueEquivalence R D).hom) := by
  have a := (@dgKNativeNuNaturality R _ P (C) _ _ inferInstance _ _
    (dgSmallPerfectEnvelope_pretriangulated R D J X) (L)).postcomp
      (dgSmallPerfectEnvelopeValueEquivalence R D J X).hom
  have b := (dgSmallPerfectEnvelopeValueEquivalence_native R D J X).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L) ≫
      (dgSmallPerfectEnvelopeNerveEquivalence R D J X).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectEnvelopeInclusion R D J X) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgSmallPerfectEnvelopeFunctorLift_inclusion]
  have b' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L) ≫ dgKNativeValueComparison R (C) ≫
        (dgSmallPerfectEnvelopeValueEquivalence R D J X).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ (dgKNativePerfectValueEquivalence R D).hom) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, ← Category.assoc, he] using b
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using a.trans b'

end SerrePositivity.KST.SConstruction
