module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorBaseChangeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftFibrationBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorEnrichedEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparisonIso

/-!
概要：相対切断空間の底変換同型を全 left fibrations 上で豊穣自然に束ねる。
方針：高次の引き戻しと第一射影の評価の可換式を使う。
規約：元の同型の順方向を比較の成分として保持する。
使われ方：under の共同切断と引き戻しの strict transport の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：底変換の切断同型の順方向は全高次の相対射について豊穣自然。
方針：相対射の合成を各次数で評価し、引き戻しの第一射影の公式を適用する。
規約：パラメーターを頂点やホモトピー類へ制限しない。
使われ方：底変換の比較を共同実現へ送る入力。 -/
def relativeFunctorBaseChangeComparison {B D : SSet.{u}} (k : D ⟶ B) (a : Over D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation ((Over.map k).obj a)) := by
  refine ⟨fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p.val.hom k a.hom, ?_⟩
  intro p q
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro x
  change t.val.app m (α ≫ 𝟙 m)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p.val.hom k a.hom).app n s).val.app m
        (α ≫ 𝟙 m) x) =
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward q.val.hom k a.hom).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeObject k p).val
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeObject k q).val).app n
          (s, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p.val.hom q.val.hom k).app n t))).val.app m α) x
  rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorBaseChangeForward_apply,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorBaseChangeForward_apply]
  change t.val.app m α ((pullback.fst p.val.hom k).app m (s.val.app m α x)) =
    (pullback.fst q.val.hom k).app m
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p.val.hom q.val.hom k).app n t).val.app m
        (α ≫ 𝟙 m) (s.val.app m (α ≫ 𝟙 m) x))
  rw [Category.comp_id]
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullback_apply_fst p.val.hom q.val.hom k t α
    (s.val.app m α x)).symm

/-- 概要：底変換の比較の各成分は既存の相対関手空間の同型そのもの。
方針：同型の順方向を比較の定義へ展開する。
規約：別の同値の選択へ置き換えない。
使われ方：全パラメーターの比較の可逆性。 -/
lemma relativeFunctorBaseChangeComparison_component {B D : SSet.{u}}
    (k : D ⟶ B) (a : Over D) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    (relativeFunctorBaseChangeComparison k a).val p =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p.val.hom k a.hom).hom := rfl

/-- 概要：底変換の相対切断の比較は全対象上で関手同型へ実現される。
方針：元の同型の成分の同値性を豊穣比較の可逆性判定に用いる。
規約：全高次の自然性は既に比較に記録されている。
使われ方：strict transport の各添字での底変換の比較。 -/
def relativeFunctorBaseChangeComparisonIso {B D : SSet.{u}} (k : D ⟶ B) (a : Over D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation ((Over.map k).obj a))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonIso (relativeFunctorBaseChangeComparison k a)
  intro p
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p.val.hom k a.hom)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
