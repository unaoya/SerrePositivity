module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictLeftSectionRestriction

/-!
概要：相対切断の共同 weighted 評価は、底の任意の単体的制限と全高次で厳密に可換。
方針：各初区間の係数で同じ評価の制限公式を適用し、Yoneda の自然性でパラメータを戻す。
規約：面・退化・一般の底上の制限を同じ一つの射の等式として扱う。
使われ方：strict 分類像との比較を底の全単体の一つの系に束ねる。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {B A D : SSet.{u}}
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (a : A ⟶ B) (k : D ⟶ A)

/-- 元の全評価は、相対切断の全図式を同時に制限する射と厳密に可換。 -/
lemma weightedLeftSectionEvaluation_restriction :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (CategoryTheory.Functor.whiskerRight
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionRestriction F a k) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ▷ D) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedLeftSectionEvaluation F (k ≫ a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F a ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ◁ k) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedLeftSectionEvaluation F a := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨σ, τ⟩, t⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  change lift (τ.app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre (F.obj (σ.obj i)).val.hom a k)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫ SSet.yonedaEquiv.symm t) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation F (k ≫ a)).app (σ.obj i) =
    lift (τ.app i)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫
        SSet.yonedaEquiv.symm (k.app _ t)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation F a).app (σ.obj i)
  rw [← lift_whiskerRight, Category.assoc]
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation_restriction F a k (σ.obj i)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre (F.obj (σ.obj i)).val.hom a k ▷ D) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation F (k ≫ a)).app (σ.obj i) = _ at hr
  rw [hr, ← Category.assoc]
  refine (congrArg (fun g ↦ g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation F a).app (σ.obj i))
    (lift_whiskerLeft (τ.app i)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫ SSet.yonedaEquiv.symm t) k)).trans ?_
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
