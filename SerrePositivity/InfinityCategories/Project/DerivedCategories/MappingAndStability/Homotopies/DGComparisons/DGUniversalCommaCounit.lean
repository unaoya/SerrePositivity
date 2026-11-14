module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugUnlifted
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGUniversalCommaNerve
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
/-- 普遍余単位のラベルを、同じ反対 comma の実対象へ評価する。 -/
def dgUniversalCommaEvaluation : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalComma R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R Cᵒᵖ Eᵒᵖ F.op)ᵒᵖ := _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation R _
/-- 比較の反対での始点を、元の同じ標的射影へ戻す。 -/
lemma dgUniversalCommaAugmentationSource_op :
    ((dgUniversalCommaEvaluation R C E F).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R Cᵒᵖ Eᵒᵖ F.op).op).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDoubleOppositeDown R E) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F := rfl
/-- 比較の反対での終点を、元の同じ始域射影の像へ戻す。 -/
lemma dgUniversalCommaAugmentationTarget_op :
    ((dgUniversalCommaEvaluation R C E F).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R Cᵒᵖ Eᵒᵖ F.op).op).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDoubleOppositeDown R E) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaSource R C E F).comp F := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgUniversalCommaEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget, DGFunctor.op, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDoubleOppositeDown,
    _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource, Category.id_comp, Category.comp_id,
    eqToHom_refl]
/-- 実普遍余単位の同じ二射影の全関手ホモトピー。 -/
def dgUniversalCommaCounitHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaSource R C E F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F)) := by
  let K := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R Cᵒᵖ Eᵒᵖ F.op
  let A := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R Cᵒᵖ Eᵒᵖ F.op
  let B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R Cᵒᵖ Eᵒᵖ F.op
  let e := dgUniversalCommaEvaluation R C E F
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDoubleOppositeDown R E
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeHomotopy R K Eᵒᵖ A B
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationUnliftedHomotopy R Cᵒᵖ Eᵒᵖ F.op))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map e)
  refine { h := H.h, h₀ := H.h₀.trans ?_, h₁ := H.h₁.trans ?_, rel := H.rel }
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map B.op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaSource R C E F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
      dgUniversalCommaAugmentationTarget_op, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map A.op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F)
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
      dgUniversalCommaAugmentationSource_op]
/-- 同じ厳密切断に沿う右随伴候補の実余単位の全関手ホモトピー。 -/
def dgUniversalRightAdjointCounitHomotopy
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y)) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R C E F h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (𝟙 _) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (dgUniversalCommaCounitHomotopy R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaNerveEquivalence R C E F h).inv
  refine { h := H.h, h₀ := ?_, h₁ := H.h₁.trans ?_, rel := H.rel }
  · exact H.h₀.trans (Category.assoc _ _ _).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaNerveEquivalence_inv_hom R C E F h
/-- 同じ実余単位ホモトピーが定める h Fun の二胞体。 -/
def dgUniversalRightAdjointCounit
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R C E F h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (𝟙 _) :=
  SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (dgUniversalRightAdjointCounitHomotopy R C E F h))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
