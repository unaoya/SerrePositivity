module
public import SerrePositivity.KST.SConstruction.CoreEnrichedInclusion
public import SerrePositivity.KST.SConstruction.SExactCoreEnrichedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEnrichedExactRecovery

/-! # 元の native Kan Perf 入力族の全完全関手空間での表示
概要：元の豊穣完全 Perf 関手の core を含め、同じ全入力族を全完全関手空間で表示する。
方針：実 core 包含を厳密豊穣合成し、元の全単体と同じ通常射を回収する。
規約：入力を離散化しない。使われ方：豊穣 S• 図式の厳密 dg 入力への前合成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ全 native Kan 入力族を、全完全関手空間に表示する厳密豊穣 Perf 関手。 -/
def presentedPerfectDGFullEnrichedFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} :=
  (presentedPerfectDGEnrichedExactFunctor A).comp SSet
    (coreEnrichedInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v})

/-- 元の安定値は、同じラベル付き実 Perf のままである。 -/
lemma presentedPerfectDGFullEnrichedFunctor_obj (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGFullEnrichedFunctor A).obj C = presentedPerfectDGStableCategory A C := rfl

/-- 全 Hom の実作用は、元の同じ完全関手族への持ち上げである。 -/
lemma presentedPerfectDGFullEnrichedFunctor_map (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGFullEnrichedFunctor A).map C D =
      presentedPerfectDGExactFamilyMap A C D := rfl

/-- 通常の元の dg 入力射で、同じ元の完全な Perf 射の豊穣表示を回収する。 -/
lemma presentedPerfectDGFullEnrichedFunctor_hom
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫ (presentedPerfectDGFullEnrichedFunctor A).map C D =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv (presentedPerfectDGExactMap A F) := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    ((presentedPerfectDGEnrichedExactFunctor A).map C D ≫ _) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
      (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) :
        SSet.{max (u + 1) v})).ι) (presentedPerfectDGEnrichedExactFunctor_hom A F)).trans
          (stableExactCoreHomEquiv_inclusion (show presentedPerfectDGStableQCat A C ⟶
            presentedPerfectDGStableQCat A D from presentedPerfectDGExactMap A F)))

end SerrePositivity.KST.SConstruction
