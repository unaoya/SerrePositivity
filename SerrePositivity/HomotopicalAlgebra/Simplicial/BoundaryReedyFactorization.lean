module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BisimplicialCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.WeakFactorizationSystem

/-! # Actual Reedy boundary factorization without a value model structure -/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.BisimplicialModel.BoundaryFactorization

abbrev left : MorphismProperty (SimplexCategoryᵒᵖ ⥤ SSet.{v}) :=
  reedyLeft simplexOp (MorphismProperty.monomorphisms _)
abbrev right : MorphismProperty (SimplexCategoryᵒᵖ ⥤ SSet.{v}) :=
  reedyRight simplexOp SSet.modelCategoryQuillen.I.rlp

lemma boundary_wfs : MorphismProperty.IsWeakFactorizationSystem
    (MorphismProperty.monomorphisms SSet.{v}) SSet.modelCategoryQuillen.I.rlp := by
  let : SSet.modelCategoryQuillen.I.{v}.HasSmallObjectArgument.{v} :=
    SimplicialModel.boundaryGenerators_smallObjectArgument
  have h : MorphismProperty.IsWeakFactorizationSystem SSet.modelCategoryQuillen.I.rlp.llp
      SSet.modelCategoryQuillen.I.rlp :=
    MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)
  rw [SimplicialModel.boundaryGenerators_leftClass] at h
  exact h

lemma reedy_wfs : MorphismProperty.IsWeakFactorizationSystem left.{v} right.{v} := by
  have : MorphismProperty.IsWeakFactorizationSystem
      (MorphismProperty.monomorphisms SSet.{v}) SSet.modelCategoryQuillen.I.rlp := boundary_wfs
  exact weakFactorizationSystem (C := SSet.{v}) simplexOp
    (MorphismProperty.monomorphisms SSet.{v})
    SSet.modelCategoryQuillen.I.rlp
    (fun _ _ h => Opposite.unop_injective (SimplexCategory.ext h))
    (fun n => ⟨Opposite.op (SimplexCategory.mk n), rfl⟩)

lemma right_app {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (p : A ⟶ B) (hp : right p)
    (j : SimplexCategoryᵒᵖ) : SSet.modelCategoryQuillen.I.rlp (p.app j) := by
  have : MorphismProperty.IsWeakFactorizationSystem
      (MorphismProperty.monomorphisms SSet.{v}) SSet.modelCategoryQuillen.I.rlp := boundary_wfs
  have hM := matchingEvaluation_mem_right simplexOp j p (MorphismProperty.monomorphisms _)
    SSet.modelCategoryQuillen.I.rlp (fun g => hp g.obj.right)
  have hpb := SSet.modelCategoryQuillen.I.rlp.pullback_fst
    ((matchingComparison simplexOp j).app B) ((matchingEvaluation simplexOp j).map p) hM
  have hc := SSet.modelCategoryQuillen.I.rlp.comp_mem _ _ (hp j) hpb
  exact (relativeMatchingMap_fst simplexOp j p) ▸ hc

lemma right_app_localized {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (p : A ⟶ B) (hp : right p)
    (j : SimplexCategoryᵒᵖ) : IsIso (SimplicialModel.AnodyneHomotopy.anodyneQ.map (p.app j)) := by
  have h := right_app p hp j
  rw [← SSet.rlp_monomorphisms] at h
  exact SimplicialModel.MonoRightLiftingContraction.localized_isIso _ h

lemma left_eq_llp : left.{v} = right.{v}.llp := by
  have : MorphismProperty.IsWeakFactorizationSystem left.{v} right.{v} := reedy_wfs
  exact (MorphismProperty.llp_eq_of_wfs left right).symm

lemma initial_left (A : SimplexCategoryᵒᵖ ⥤ SSet.{v}) : left (initial.to A) := by
  intro j
  have hi : IsIso ((latchingComparison simplexOp j).app
      (⊥_ (SimplexCategoryᵒᵖ ⥤ SSet.{v}))) :=
    isIso_of_isInitial
      (initialIsInitial.isInitialObj (latchingEvaluation simplexOp j) _)
      (initialIsInitial.isInitialObj ((evaluation SimplexCategoryᵒᵖ SSet.{v}).obj j) _) _
  let e : Arrow.mk ((latchingComparison simplexOp j).app A) ≅
      Arrow.mk (relativeLatchingMap simplexOp j (initial.to A)) :=
    Arrow.isoMk (asIso (pushout.inl ((latchingEvaluation simplexOp j).map (initial.to A))
      ((latchingComparison simplexOp j).app (⊥_ (SimplexCategoryᵒᵖ ⥤ SSet.{v})))))
      (Iso.refl _) ((inl_relativeLatchingMap simplexOp j (initial.to A)).trans
        (Category.comp_id _).symm)
  exact ((MorphismProperty.monomorphisms SSet.{v}).arrow_iso_iff e).mp
    (latchingComparison_mono A j)

end SerrePositivity.BisimplicialModel.BoundaryFactorization
