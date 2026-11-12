module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexStandardTargetFactorization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramAnodyneRestriction

/-!
概要：恒等二単体の元の target 制限は、同じ元の射として自明 Kan fibration。
方針：標準内ホーンの inner anodyne 性と同じ pullback 表示の同型で移送する。
規約：元の分類図式の同じ二辺制限を保持し、同値性を追加仮定にしない。
使われ方：二単体上の同じ元の分類 Hom 作用の同値性の反映。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 恒等二単体の同じ標準内ホーンの表示は inner anodyne。 -/
lemma cocartesianTwoSimplexStandardHorn_id_innerAnodyne :
    innerAnodyneExtensions
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexStandardHorn (𝟭 (ULift.{u} (Fin 3)))) := by
  have hi : nerveMap (𝟭 (ULift.{u} (Fin 3))) = 𝟙 _ := rfl
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexStandardHorn]
  rw [hi, CategoryTheory.Functor.map_id, Category.comp_id]
  exact innerAnodyneExtensions.comp_mem _ _
    (innerAnodyneExtensions.horn_ι (by decide) (by decide))
    (innerAnodyneExtensions.of_isIso _)

variable (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))

/-- 同じ標準内ホーン上の target Segal 射は、全パラメーターで自明 Kan。 -/
lemma cocartesianTwoSimplexStandardHornTargetSegalMap_id_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexStandardHornTargetSegalMap (𝟭 _) p q) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_trivialKanFibration_of_innerAnodyne
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexStandardHorn (𝟭 (ULift.{u} (Fin 3))))
    cocartesianTwoSimplexStandardHorn_id_innerAnodyne
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ h.mem (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isIso _)⟩

/-- 恒等二単体の元の target 制限自身は、同じ元の二辺への自明 Kan 制限。 -/
lemma cocartesianTwoSimplexTargetRestrictionMap_id_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetRestrictionMap (𝟭 _) p q) := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexStandardTargetPullbackMap (𝟭 _) p q) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexStandardTargetPullbackMap_isIso _ p q
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetRestrictionMap (𝟭 _) p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexStandardHornTargetSegalMap (𝟭 _) p q ≫
        inv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexStandardTargetPullbackMap (𝟭 _) p q) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetRestrictionMap_standard_factor, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [hf]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
    (cocartesianTwoSimplexStandardHornTargetSegalMap_id_trivialKanFibration p q).mem
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isIso _)⟩

/-- 同じ元の target 制限は、追加仮定なしに quasicategory の同値。 -/
lemma cocartesianTwoSimplexTargetRestrictionMap_id_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetRestrictionMap (𝟭 _) p q) := by
  have := cocartesianTwoSimplexTargetRestrictionMap_id_trivialKanFibration p q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
