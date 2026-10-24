module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeSliceCylinderReflection
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationOldCocone
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowNativeAllBoundaryCylinder
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorEvaluationLifting
/-!
概要：元の補間族の制限と元の q を、同じ始点評価の下で slice 内に相対反映する。
方針：元の三条件固定円柱と評価の厳密一致を、slice の相対反映へ適用する。
規約：元の両全族を保ち、通常の関手同型だけへ弱めない。
使われ方：実 diagram comma の相対同型と評価の cofinal 性への帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
local notation "T" => CategoryTheory.Functor.obj SSet.uliftFunctor A
local notation "p" => SSet.yonedaEquiv.symm (functorVertex D)
local notation "e" => evaluateFunctorAt (Y := IndInfinity κ C)
  (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
local notation "f" => indArrowInterpolationOldFamily V ≫ diagramCommaSliceProjection κ D
local notation "g" => q ≫ diagramCommaSliceProjection κ D
local notation "a" => g ≫ sliceOverPostcomp p e
local notation "s" => SSet.ι₀ ≫ indArrowNormalizedPrism κ D q
/-- 概要：同じ元の補間族の slice 像は、指定始点評価を固定した相対関手空間で同型。
方針：元の全固定円柱を反映する。規約：原の q と全境界を保持。使われ方：comma への相対反映。 -/
lemma exists_indArrowInterpolationOldFamily_relative_slice_iso :
    ∃ hf : f ≫ sliceOverPostcomp p e = a,
    Nonempty (VertexIso
      (relativeFunctorVertex (sliceOverPostcomp p e) a f hf)
      (relativeFunctorVertex (sliceOverPostcomp p e) a g rfl)) := by
  have hfe : sliceOverUncurry f ≫ e = s := by
    rw [indArrowInterpolationOldFamily_uncurry V]
    exact indArrowPrismNativeAllBoundaryReconstructed_source V.slicePrism
  have hge : sliceOverUncurry g ≫ e = s := by
    rw [diagramCommaSliceProjection_uncurry]
    exact indArrowPrismNativeAllBoundaryOriginal_source V.slicePrism
  have hf : f ≫ sliceOverPostcomp p e = a := by
    apply sliceOverUncurry_injective
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_postcomp, hfe, hge]
  obtain ⟨U, h₀, h₁, _, hTip, hEval⟩ := exists_indArrowNativeAllBoundaryCylinder V.slicePrism
  have ht : (joinInr T Δ[0] ▷ equivalenceInterval) ≫ U =
      CategoryTheory.CartesianMonoidalCategory.fst (Δ[0] : SSet.{u + 1}) equivalenceInterval ≫ p :=
    hTip.trans (congrArg (fun k =>
      CategoryTheory.CartesianMonoidalCategory.fst (Δ[0] : SSet.{u + 1}) equivalenceInterval ≫ k)
        (indArrowNormalizedPrism_curry_tip κ D))
  refine ⟨hf, nonempty_sliceRelativeFunctorVertexIso_of_coconeCylinder p e
    (kanEquivalenceLifting_evaluateFunctorAt _) f g a hf rfl U ?_ ?_ ht ?_⟩
  · exact h₀.trans (indArrowInterpolationOldFamily_uncurry V).symm
  · exact h₁.trans (diagramCommaSliceProjection_uncurry q).symm
  · rw [hfe]
    exact hEval
end SerrePositivity.InfinityCategories.F2.Ind
