module
public import SerrePositivity.KST.SConstruction.SExactCoreEnrichedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEnrichedExactRecovery

/-! # 元の全厳密 dg 入力からの厳密豊穣 S_n Perf 関手
概要：元の豊穣完全 Perf 関手と全パラメータ S_n を厳密豊穣合成する。
方針：元の全 native Kan 入力と完全関手空間の実 core をそのまま接続する。
規約：BF K 値化は後続。使われ方：反復 S•・実現のための実 dg 入力関手。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の全 native dg 入力族を保つ、同じ実 S_n Perf の厳密豊穣関手。 -/
def presentedPerfectDGSEnrichedFunctor (n : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{max (u + 1) v} :=
  (presentedPerfectDGEnrichedExactFunctor A).comp SSet (sExactCoreEnrichedEndofunctor n)

/-- 実値は、元のラベル付き Perf の全 gapped S_n と同じ安定模型。 -/
lemma presentedPerfectDGSEnrichedFunctor_obj (n : ℕ) (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGSEnrichedFunctor A n).obj C).obj =
      sConstruction n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C)) := rfl

/-- 全 Hom の作用は、元の豊穣完全 Perf 作用と実 S_n の core 作用との合成。 -/
lemma presentedPerfectDGSEnrichedFunctor_map (n : ℕ) (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGSEnrichedFunctor A n).map C D =
      (presentedPerfectDGEnrichedExactFunctor A).map C D ≫
        (sExactCoreEnrichedEndofunctor n).map
          (presentedPerfectDGStableQCat A C) (presentedPerfectDGStableQCat A D) := rfl

/-- 元の通常の dg 入力射では、同じ実 Perf 作用の cofiber 型 S_n 後合成を回収する。 -/
lemma presentedPerfectDGSEnrichedFunctor_hom (n : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫ (presentedPerfectDGSEnrichedFunctor A n).map C D =
      eHomEquiv SSet.{max (u + 1) v} (show (presentedPerfectDGSEnrichedFunctor A n).obj C ⟶
        (presentedPerfectDGSEnrichedFunctor A n).obj D from
          sExactMap n (presentedPerfectDGExactMap A F)) := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    ((presentedPerfectDGEnrichedExactFunctor A).map C D ≫
      (sExactCoreEnrichedEndofunctor n).map
        (presentedPerfectDGStableQCat A C) (presentedPerfectDGStableQCat A D)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (sExactCoreEnrichedEndofunctor n).map
      (presentedPerfectDGStableQCat A C) (presentedPerfectDGStableQCat A D))
        (presentedPerfectDGEnrichedExactFunctor_hom A F)).trans
          (sExactCoreEnrichedEndofunctor_hom n (show presentedPerfectDGStableQCat A C ⟶
            presentedPerfectDGStableQCat A D from presentedPerfectDGExactMap A F)))

end SerrePositivity.KST.SConstruction
