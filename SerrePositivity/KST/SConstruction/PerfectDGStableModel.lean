module
public import SerrePositivity.KST.SConstruction.DGModuleClosedStability
public import SerrePositivity.KST.SConstruction.DGApplication
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuasiEquivalenceNerve

/-! # 射影的 perfect dg 加群と小さい代表系の実安定模型
概要：Perf の全 dg enhancement と小さい代表系の native nerve を安定入力にする。
方針：実有限操作の閉性を使い、小さい代表系の準同値包含で安定性を輸送する。
規約：対象を縮小した宇宙への移行・関手的 Perf は別工程。使われ方：K-4d の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 射影的 perfect 加群は実零加群・cone・fiber で閉じる。 -/
lemma perfectDGClosedOperations (S : Set D) :
    DGModuleClosedOperations A D (modulePerfectProjectiveOver A D S) where
  zero_mem := modulePerfectProjectiveOver_zero A D S
  cone_mem f hM hN := modulePerfectProjectiveOver_cone A D hM hN f
  fiber_mem f hM hN := modulePerfectProjectiveOver_shift A D
    (modulePerfectProjectiveOver_cone A D hM hN f) (-1)

/-- 全射影的 perfect dg 加群の native nerve による安定入力。 -/
def perfectDGStableModel (S : Set D) : StableModel.{max (u + 1) v} :=
  dgModuleClosedStableModel A D _ (perfectDGClosedOperations A D S)

/-- 小さい代表系の実 dg 包含が与える native nerve の実同値。 -/
def smallPerfectDGNerveEquivalence (S : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (SmallPerfectDGModuleOver A D S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PerfectDGModuleOver A D S)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuasiEquivalenceNerveEquivalence (smallPerfectDGModuleInclusion A D S)
    (smallPerfectDGModuleInclusion_quasiEquivalence A D S)

/-- 小さい代表系の nerve の安定性を全写像空間の同値で反映する。 -/
lemma smallPerfectDGNerve_isStable (S : Set D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (SmallPerfectDGModuleOver A D S)) :=
  (smallPerfectDGNerveEquivalence A D S).isStable_iff.mpr
    (perfectDGStableModel A D S).stable

/-- 小さい対象族による Perf の native nerve を安定入力に束ねる。 -/
def smallPerfectDGStableModel (S : Set D) : StableModel.{max (u + 1) v} where
  carrier := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (SmallPerfectDGModuleOver A D S)
  quasicategory := inferInstance
  stable := smallPerfectDGNerve_isStable A D S

end SerrePositivity.KST.SConstruction
