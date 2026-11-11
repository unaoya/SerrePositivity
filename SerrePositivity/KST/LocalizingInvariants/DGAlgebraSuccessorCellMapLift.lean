module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSuccessorCellMapPrimitives
public import SerrePositivity.DifferentialGraded.Resolution.Cell

/-!
概要：全射擬同型に沿う任意の次段の射の厳密な cell 延長。
方針：指定原始元を持ち上げ、元の付加圏の全関手の一意性で合成を照合する。
規約：元の増大射に限定せず、指定した次段の射を保つ。
使われ方：cell 源の任意射の全段持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGCategoryCellResolution
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)}

def successorCellMapTargetFunctor (n : ℕ) (b : cellStage R A (n + 1) ⟶ B) :
    let S := stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) n
    let SI := S.CellIndex
    let SC := S.cells
    letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) := S.category
    DGFunctor R (SC.Objects R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) SI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) := by
  let S := stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) n
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) := S.category
  exact
    { obj := fun _ => .star
      map := fun x y => by rcases x with ⟨x⟩; rcases y with ⟨y⟩; cases x; cases y; exact b.hom
      map_id := fun x => by rcases x with ⟨x⟩; cases x; exact IsMonHom.one_hom b.hom
      map_comp := fun x y z => by
        rcases x with ⟨x⟩; rcases y with ⟨y⟩; rcases z with ⟨z⟩
        cases x; cases y; cases z; exact IsMonHom.mul_hom b.hom }

variable (p : C ⟶ B) (hs : ∀ k : ℤ, Function.Surjective (p.hom.f k))
  (hq : QuasiIso p.hom) (n : ℕ) (a : cellStage R A n ⟶ C)
  (b : cellStage R A (n + 1) ⟶ B) (ha : a ≫ p = cellStageTransition R A n ≫ b)

def successorCellMapLift : cellStage R A (n + 1) ⟶ C := by
  let P := successorCellMapPrimitives R p hs hq n a b ha
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) := (stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) n).category
  exact Mon.Hom.mk' (P.attachedEvaluation .star .star)
    (P.attachedEvaluation_unit .star) (P.attachedEvaluation_composition .star .star .star)

lemma successorCellMapLift_transition :
    cellStageTransition R A n ≫ successorCellMapLift R p hs hq n a b ha = a := by
  apply Mon.Hom.ext'
  let P := successorCellMapPrimitives R p hs hq n a b ha
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) := (stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) n).category
  exact P.attachedEvaluation_original .star .star

lemma successorCellMapLiftFunctor_projection :
    let S := stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) n
    let P := successorCellMapPrimitives R p hs hq n a b ha
    letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) := S.category
    P.extension.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R p) = successorCellMapTargetFunctor R n b := by
  let S := stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) n
  let P := successorCellMapPrimitives R p hs hq n a b ha
  let SI := S.CellIndex
  let SC := S.cells
  let SD := S.category
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) := SD
  have hp := successorCellMapPrimitives_projection R p hs hq n a b ha
  apply @DGCellAttachment.Family.functor_ext R _ _ SD SI SC _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointEnrichment R B) _
  · apply @EnrichedFunctor.ext (Complex R) _ _ _ _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointEnrichment R B) _ _ (fun x => by cases x; rfl)
    intro x y
    cases x; cases y
    change (_ ≫ (_ ≫ p.hom)) ≫ eqToHom (by rfl) = _
    rw [eqToHom_refl, Category.comp_id, ← Category.assoc]
    have ho := @DGCellAttachment.Family.PrimitiveData.attachedEvaluation_original R _ _ SD
      SI _ SC _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointEnrichment R C) _ P .star .star
    exact (congrArg (fun f => f ≫ p.hom) ho).trans (congrArg Mon.Hom.hom ha)
  · apply heq_of_eq
    funext i
    have hP := @DGCellAttachment.Family.PrimitiveData.attachedEvaluation_generator R _ _ SD
      SI _ SC _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointEnrichment R C) _ P i
    have h := (congrArg (p.hom.f i.2.2.degree) hP).trans (hp i)
    rcases i with ⟨x, y, c⟩
    cases x; cases y
    exact h

lemma successorCellMapLift_projection : successorCellMapLift R p hs hq n a b ha ≫ p = b := by
  apply Mon.Hom.ext'
  have h := successorCellMapLiftFunctor_projection R p hs hq n a b ha
  let S := stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) n
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) := S.category
  exact eq_of_heq (@DGFunctor.hcongr_map R _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointEnrichment R B)
    _ _ h ⟨.star⟩ ⟨.star⟩)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
