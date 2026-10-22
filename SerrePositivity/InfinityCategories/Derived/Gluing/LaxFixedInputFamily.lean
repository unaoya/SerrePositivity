module
public import SerrePositivity.InfinityCategories.F2.LaxPullbackLift
public import SerrePositivity.InfinityCategories.F1.IntervalFatDiagram

/-! 固定した二入力の間の全区間 Hom を、同じ矢印族の lax pullback の部分族へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
  (a : A _⦋0⦌) (b : B _⦋0⦌)

def dgGluingIntervalArrowFamily (x y : C _⦋0⦌) :
    intervalMappingSpace x y ⟶ (ihom (Δ[1] : SSet.{u})).obj C :=
  curry (intervalMappingUncurry (𝟙 (intervalMappingSpace x y)))

lemma dgGluingIntervalArrowFamily_source (x y : C _⦋0⦌) :
    dgGluingIntervalArrowFamily x y ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
      SSet.const x := by
  rw [dgGluingIntervalArrowFamily, curry_evaluateFunctorAt_interval, intervalMappingUncurry_zero]

lemma dgGluingIntervalArrowFamily_target (x y : C _⦋0⦌) :
    dgGluingIntervalArrowFamily x y ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
      SSet.const y := by
  rw [dgGluingIntervalArrowFamily, curry_evaluateFunctorAt_interval, intervalMappingUncurry_one]

lemma dgGluingIntervalArrowFamily_eq (x y : C _⦋0⦌) :
    dgGluingIntervalArrowFamily x y =
      vertexFiberι ((pre (boundary 1).ι).app C) (functorVertex (intervalMappingBoundary x y)) := by
  change curry (uncurry (𝟙 _ ≫ _)) = _
  rw [Category.id_comp, curry_uncurry]

def dgGluingLaxFixedInputFamily :
    intervalMappingSpace (p.app _ a) (q.app _ b) ⟶ F2.laxPullback p q :=
  F2.laxPullbackLift p q (SSet.const a) (SSet.const b)
    (dgGluingIntervalArrowFamily (p.app _ a) (q.app _ b))
    (by rw [dgGluingIntervalArrowFamily_source, SSet.const_comp])
    (by rw [dgGluingIntervalArrowFamily_target, SSet.const_comp])

lemma dgGluingLaxFixedInputFamily_arrow :
    dgGluingLaxFixedInputFamily p q a b ≫ F2.laxPullbackArrow p q =
      dgGluingIntervalArrowFamily (p.app _ a) (q.app _ b) :=
  F2.laxPullbackLift_arrow _ _ _ _ _ _ _

lemma dgGluingLaxFixedInputFamily_left :
    dgGluingLaxFixedInputFamily p q a b ≫ F2.laxPullbackFst p q = SSet.const a :=
  F2.laxPullbackLift_fst _ _ _ _ _ _ _

lemma dgGluingLaxFixedInputFamily_right :
    dgGluingLaxFixedInputFamily p q a b ≫ F2.laxPullbackSnd p q = SSet.const b :=
  F2.laxPullbackLift_snd _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
