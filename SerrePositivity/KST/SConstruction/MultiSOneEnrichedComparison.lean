module
public import SerrePositivity.KST.SConstruction.SOneFamilyComparison
public import SerrePositivity.KST.SConstruction.MultiSQuasicategoryEnrichedFunctor
public import SerrePositivity.KST.SConstruction.SExactQuasicategoryDiagram
public import SerrePositivity.KST.SConstruction.MultiSOneComparison

/-! # 全有限反復 S₁ 比較の全族自然性
概要：元の先頭 S₁ 比較を、全高次比較として有限反復の各多次数に保持する。
方針：元の S₁ 全族比較で、残りの反復の豊穣関手を前合成する。
規約：自然な逆射は選ばない。使われ方：native dg の同じ core・実現・境界商比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 同じ元の S₁ 比較を、全高次完全関手族に自然な比較として保持する。 -/
def sOneQuasicategoryEnrichedComparison :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison (sExactQuasicategoryEnrichedFunctor.{u} 1)
      stableQuasicategoryEnrichedInclusion := by
  refine ⟨fun C => sOneComparison C.obj, ?_⟩
  intro C D
  change (sOneComparison C.obj ▷ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})) ≫
    uncurry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι =
      uncurry (sExactFamilyMap 1 C D) ≫ sOneComparison D.obj
  rw [sExactFamilyMap, uncurry_curry]
  exact sOneComparison_family_action C D

/-- 有限反復の元の先頭 S₁ 比較は、全高次入力族に厳密に自然である。 -/
def multiSOneQuasicategoryEnrichedComparison (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison
      (multiSQuasicategoryEnrichedFunctor.{u} (r + 1) ((oneDirectionIndex r).obj d))
      (multiSQuasicategoryEnrichedFunctor r d) := by
  refine ⟨fun C => sOneComparison (multiSExactCategory r d C).obj, ?_⟩
  intro C D
  have h := (sOneQuasicategoryEnrichedComparison.precompose
    (multiSExactEnrichedEndofunctor r d)).property C D
  rw [multiSQuasicategoryEnrichedFunctor_map_succ]
  exact h

end SerrePositivity.KST.SConstruction
