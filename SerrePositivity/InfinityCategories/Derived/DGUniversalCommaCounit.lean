module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugUnlifted
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGUniversalCommaNerve
/-!
概要：普遍余単位の同じ比較 cochain から、実二射影と厳密切断の全関手ホモトピーを作る。
方針：一般 comma の実 prism を反対 nerve と二重反対の実 dg 射影へ移す。
規約：同じ厳密切断を保持する。使われ方：右随伴候補の実余単位と ∞ 随伴の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
  [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
/-- 普遍余単位のラベルを、同じ反対 comma の実対象へ評価する。 -/
def dgUniversalCommaEvaluation : DGFunctor R (DGUniversalComma R C E F)
    (DGFunctorCommaObject R Cᵒᵖ Eᵒᵖ F.op)ᵒᵖ := dgObjectImageEvaluation R _
/-- 比較の反対での始点を、元の同じ標的射影へ戻す。 -/
lemma dgUniversalCommaAugmentationSource_op :
    ((dgUniversalCommaEvaluation R C E F).comp
      (dgCommaAugmentationSource R Cᵒᵖ Eᵒᵖ F.op).op).comp (dgDoubleOppositeDown R E) =
      dgUniversalCommaTarget R C E F := rfl
/-- 比較の反対での終点を、元の同じ始域射影の像へ戻す。 -/
lemma dgUniversalCommaAugmentationTarget_op :
    ((dgUniversalCommaEvaluation R C E F).comp
      (dgCommaAugmentationTarget R Cᵒᵖ Eᵒᵖ F.op).op).comp (dgDoubleOppositeDown R E) =
      (dgUniversalCommaSource R C E F).comp F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgUniversalCommaEvaluation,
    dgCommaAugmentationTarget, DGFunctor.op, dgDoubleOppositeDown,
    dgObjectImageEvaluation, dgFunctorCommaSource, Category.id_comp, Category.comp_id,
    eqToHom_refl]
/-- 実普遍余単位の同じ二射影の全関手ホモトピー。 -/
def dgUniversalCommaCounitHomotopy :
    SSet.Homotopy (dgNerve.map (dgUniversalCommaSource R C E F) ≫ dgNerve.map F)
      (dgNerve.map (dgUniversalCommaTarget R C E F)) := by
  let K := DGFunctorCommaObject R Cᵒᵖ Eᵒᵖ F.op
  let A := dgCommaAugmentationSource R Cᵒᵖ Eᵒᵖ F.op
  let B := dgCommaAugmentationTarget R Cᵒᵖ Eᵒᵖ F.op
  let e := dgUniversalCommaEvaluation R C E F
  let d := dgDoubleOppositeDown R E
  let H := functorHomotopyPrecomp
    (functorHomotopyPostcomp
      (dgNerveOppositeHomotopy R K Eᵒᵖ A B
        (dgCommaAugmentationUnliftedHomotopy R Cᵒᵖ Eᵒᵖ F.op))
      (dgNerve.map d)) (dgNerve.map e)
  refine { h := H.h, h₀ := H.h₀.trans ?_, h₁ := H.h₁.trans ?_, rel := H.rel }
  · change dgNerve.map e ≫ dgNerve.map B.op ≫ dgNerve.map d =
      dgNerve.map (dgUniversalCommaSource R C E F) ≫ dgNerve.map F
    rw [← Category.assoc, ← dgNerve.map_comp, ← dgNerve.map_comp,
      dgUniversalCommaAugmentationTarget_op, dgNerve.map_comp]
  · change dgNerve.map e ≫ dgNerve.map A.op ≫ dgNerve.map d =
      dgNerve.map (dgUniversalCommaTarget R C E F)
    rw [← Category.assoc, ← dgNerve.map_comp, ← dgNerve.map_comp,
      dgUniversalCommaAugmentationSource_op]
/-- 同じ厳密切断に沿う右随伴候補の実余単位の全関手ホモトピー。 -/
def dgUniversalRightAdjointCounitHomotopy
    (h : ∀ y : E, Nonempty (DGUniversalCounit R C E F y)) :
    SSet.Homotopy (dgUniversalRightAdjointCandidate R C E F h ≫ dgNerve.map F) (𝟙 _) := by
  let H := functorHomotopyPrecomp (dgUniversalCommaCounitHomotopy R C E F)
    (dgUniversalCommaNerveEquivalence R C E F h).inv
  refine { h := H.h, h₀ := ?_, h₁ := H.h₁.trans ?_, rel := H.rel }
  · exact H.h₀.trans (Category.assoc _ _ _).symm
  · exact dgUniversalCommaNerveEquivalence_inv_hom R C E F h
/-- 同じ実余単位ホモトピーが定める h Fun の二胞体。 -/
def dgUniversalRightAdjointCounit
    (h : ∀ y : E, Nonempty (DGUniversalCounit R C E F y)) :
    FunctorHom (dgUniversalRightAdjointCandidate R C E F h ≫ dgNerve.map F) (𝟙 _) :=
  SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (dgUniversalRightAdjointCounitHomotopy R C E F h))
end SerrePositivity.InfinityCategories
