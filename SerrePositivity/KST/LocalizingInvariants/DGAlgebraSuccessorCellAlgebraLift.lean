module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSuccessorCellPrimitives
public import SerrePositivity.DifferentialGraded.Resolution.Cell

/-!
概要：段階代数射を全境界 cell の付加へ延長し、元の増大との合成を保つ。
方針：指定原始元の実評価と、生成辺・cell に関する延長の一意性を使う。
規約：源・標的の dg instance を混同しない。使われ方：全 cell 分解の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGCategoryCellResolution
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  (n : ℕ) (g : cellStage R B n ⟶ C) (hg : g ≫ p = cellStageAugmentation R B n)

def successorCellAlgebraLift : cellStage R B (n + 1) ⟶ C := by
  let S := stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n
  let P := successorCellPrimitives R p hs hq n g hg
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) := S.category
  exact Mon.Hom.mk' (P.attachedEvaluation .star .star)
    (P.attachedEvaluation_unit .star) (P.attachedEvaluation_composition .star .star .star)

lemma successorCellAlgebraLift_transition :
    cellStageTransition R B n ≫ successorCellAlgebraLift R p hs hq n g hg = g := by
  apply Mon.Hom.ext
  let S := stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n
  let P := successorCellPrimitives R p hs hq n g hg
  let : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) := S.category
  exact P.attachedEvaluation_original .star .star

lemma successorCellLiftFunctor_projection :
    let S := stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n
    let P := successorCellPrimitives R p hs hq n g hg
    let Q := S.cellPrimitives
    let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R p
    let SD := S.category
    letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) := SD
    @DGFunctor.comp R _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment R B) P.extension G =
      @DGCellAttachment.Family.PrimitiveData.extension R _ _ SD _ _ _ _
        (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment R B) _ Q := by
  let S := stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n
  let P := successorCellPrimitives R p hs hq n g hg
  let Q := S.cellPrimitives
  let SC := S.cells
  let SI := S.CellIndex
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R p
  let st := S.transition
  let sa := S.attach.map
  have ht := S.transition_augmentation
  have ha := congrArg Mon.Hom.hom hg
  have hp := successorCellPrimitives_projection R p hs hq n g hg
  let SD := S.category
  let : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) := SD
  apply @DGCellAttachment.Family.functor_ext R _ _ SD SI SC _
    (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment R B) _
  · apply @EnrichedFunctor.ext (Complex R) _ _ _ _ _
      (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment R B) _ _ (fun x => by cases x; rfl)
    intro x y
    cases x; cases y
    change (_ ≫ (_ ≫ p.hom)) ≫ eqToHom (by rfl) = _
    rw [eqToHom_refl, Category.comp_id, ← Category.assoc]
    have ho := @DGCellAttachment.Family.PrimitiveData.attachedEvaluation_original R _ _ SD
      SI _ SC _ (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment R C) _ P .star .star
    exact ((congrArg (fun f => f ≫ p.hom) ho).trans ha).trans (ht .star .star).symm
  · apply heq_of_eq
    funext i
    have hP := @DGCellAttachment.Family.PrimitiveData.attachedEvaluation_generator R _ _ SD
      SI _ SC _ (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment R C) _ P i
    have hQ := @DGCellAttachment.Family.PrimitiveData.attachedEvaluation_generator R _ _ SD
      SI _ SC _ (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment R B) _ Q i
    exact (congrArg (p.hom.f i.2.2.degree) hP).trans ((hp i).trans hQ.symm)

lemma successorCellAlgebraLift_projection :
    successorCellAlgebraLift R p hs hq n g hg ≫ p = cellStageAugmentation R B (n + 1) := by
  apply Mon.Hom.ext
  have h := successorCellLiftFunctor_projection R p hs hq n g hg
  let S := stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n
  let : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) := S.category
  exact eq_of_heq (@DGFunctor.hcongr_map R _ _ _ _ (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment R B)
    _ _ h ⟨.star⟩ ⟨.star⟩)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
