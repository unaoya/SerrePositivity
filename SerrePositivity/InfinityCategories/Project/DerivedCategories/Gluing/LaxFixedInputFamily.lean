module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFatDiagram

/-! 固定した二入力の間の全区間 Hom を、同じ矢印族の lax pullback の部分族へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
  (a : A _⦋0⦌) (b : B _⦋0⦌)

def dgGluingIntervalArrowFamily (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⟶ (ihom (Δ[1] : SSet.{u})).obj C :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)))

lemma dgGluingIntervalArrowFamily_source (x y : C _⦋0⦌) :
    dgGluingIntervalArrowFamily x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
      SSet.const x := by
  rw [dgGluingIntervalArrowFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero]

lemma dgGluingIntervalArrowFamily_target (x y : C _⦋0⦌) :
    dgGluingIntervalArrowFamily x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
      SSet.const y := by
  rw [dgGluingIntervalArrowFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one]

lemma dgGluingIntervalArrowFamily_eq (x y : C _⦋0⦌) :
    dgGluingIntervalArrowFamily x y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)) := by
  change curry (uncurry (𝟙 _ ≫ _)) = _
  rw [Category.id_comp, curry_uncurry]

def dgGluingLaxFixedInputFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (p.app _ a) (q.app _ b) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift p q (SSet.const a) (SSet.const b)
    (dgGluingIntervalArrowFamily (p.app _ a) (q.app _ b))
    (by rw [dgGluingIntervalArrowFamily_source, SSet.const_comp])
    (by rw [dgGluingIntervalArrowFamily_target, SSet.const_comp])

lemma dgGluingLaxFixedInputFamily_arrow :
    dgGluingLaxFixedInputFamily p q a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q =
      dgGluingIntervalArrowFamily (p.app _ a) (q.app _ b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_arrow _ _ _ _ _ _ _

lemma dgGluingLaxFixedInputFamily_left :
    dgGluingLaxFixedInputFamily p q a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q = SSet.const a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_fst _ _ _ _ _ _ _

lemma dgGluingLaxFixedInputFamily_right :
    dgGluingLaxFixedInputFamily p q a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q = SSet.const b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_snd _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
