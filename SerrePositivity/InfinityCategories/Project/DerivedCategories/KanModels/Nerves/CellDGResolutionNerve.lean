module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorTrivialFibration
public import SerrePositivity.DifferentialGraded.Resolution.Cell

/-! # 生成元添加による平坦 dg 分解の nerve の同値

概要：具体的な cell 分解の増大関手は、nerve 上の自明 Kan fibration と明示的同値を与える。
方針：閉元の持ち上げと第一境界添加から各次数全射性を示し、既存 Hom 準同型性と合わせる。
規約：L4 §26〜27 と同じ構成を基盤の公開部品で使う。使われ方：β3 の平坦模型。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory HomologicalComplex DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 第一境界添加の増大射は各次数で全射。 -/
lemma dgCellFirstStage_degree_surjective (x y : D) (n : ℤ) :
    Function.Surjective ((DGCategoryCellResolution.stageAugmentation A D 1 x y).f n) := by
  intro b
  let K := homObject A D x y
  let z : complexCycles A K (n + 1) := ⟨K.d n (n + 1) b, by
    change K.d (n + 1) (n + 1 + 1) (K.d n (n + 1) b) = 0
    exact congrArg (fun f => f b) (K.d_comp_d n (n + 1) (n + 1 + 1))⟩
  obtain ⟨t, ht⟩ := DGCategoryCycleCover.cycle_lift A D x y (n + 1) z
  let c : ComplexBoundaryCell A (DGCategoryCellResolution.stageAugmentation A D 0 x y) :=
    ⟨n, t, b, ht.symm⟩
  obtain ⟨a, _, ha⟩ := DGCategoryCellResolution.stage_fills A D 0 x y c
  exact ⟨a, ha⟩

/-- 具体的な cell 分解の増大関手の Hom は各次数で全射。 -/
lemma dgCellAugmentation_degree_surjective
    (x y : DGCategoryCellResolution.Source A D) (n : ℤ) :
    Function.Surjective (((DGCategoryCellResolution.augmentation A D).map x y).f n) := by
  intro b
  obtain ⟨a, ha⟩ := dgCellFirstStage_degree_surjective A D x.val y.val n b
  refine ⟨(DGCategoryCellResolution.stageInclusion A D 1 x.val y.val).f n a, ?_⟩
  have h := congrArg (fun f => f.f n a)
    (DGCategoryCellResolution.stageInclusion_augmentation A D 1 x.val y.val)
  exact h.trans ha

/-- 具体的な cell 分解の増大関手は対象でも全射。 -/
lemma dgCellAugmentation_obj_surjective :
    Function.Surjective (DGCategoryCellResolution.augmentation A D).obj :=
  fun x => ⟨⟨x⟩, rfl⟩

/-- cell 分解の増大関手の nerve は自明 Kan fibration。 -/
instance dgCellAugmentationNerve_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_trivialKanFibration_of_surjective_quasiIso _
    (dgCellAugmentation_obj_surjective A D) (dgCellAugmentation_degree_surjective A D)
    (DGCategoryCellResolution.augmentation_homQuasiIso A D)

/-- cell 分解の増大関手の nerve は ∞ 圏同値。 -/
lemma dgCellAugmentationNerve_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

/-- 平坦分解の nerve と元の nerve の明示的な ∞ 圏同値。 -/
def dgCellResolutionNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGCategoryCellResolution.Source A D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D))

/-- 選んだ同値の順方向は、実際の増大関手の nerve そのもの。 -/
lemma dgCellResolutionNerveEquivalence_hom :
    (dgCellResolutionNerveEquivalence A D).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
