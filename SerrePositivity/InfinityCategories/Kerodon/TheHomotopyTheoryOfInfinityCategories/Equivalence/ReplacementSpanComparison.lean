module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SpanPullbackLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyPathParameters

/-!
概要：三対象の span の可逆 path 置換と、指定した元の比較の回収。
方針：始点比較の二射影を交換し、標準切断の自然性を用いる。
規約：元の span と全ての可換等式を保持する。
使われ方：同値な局所化比較の pullback による貼り合わせ。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- span の相対比較に合わせ、始点比較の二つの射影を交換する。 -/
def replacementSquareStartCornerFlipped {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement u ⟶ pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareStartCorner u v p q h ≫
    (pullbackSymmetry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p).hom

/-- 交換した始点比較の第一射影は元の始域への射影。 -/
lemma replacementSquareStartCornerFlipped_fst {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    replacementSquareStartCornerFlipped u v p q h ≫
        pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u := by
  rw [replacementSquareStartCornerFlipped, Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact pullback.lift_snd _ _ _

/-- 交換した始点比較の第二射影は四角形の同時解像。 -/
lemma replacementSquareStartCornerFlipped_snd {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    replacementSquareStartCornerFlipped u v p q h ≫
        pullback.snd p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h := by
  rw [replacementSquareStartCornerFlipped, Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact pullback.lift_fst _ _ _

/-- 始点比較の全境界持ち上げは、二つの射影を交換しても保たれる。 -/
instance replacementSquareStartCornerFlipped_trivialKanFibration {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt q 0)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (replacementSquareStartCornerFlipped u v p q h) := by
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareStartCorner u v p q h))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p :=
      (pullbackSymmetry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p).hom))⟩

/-- 可逆 path 置換の標準切断は、元の可換四角形に厳密に自然。 -/
lemma replacementSquareMap_section {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h =
      p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection v := by
  have hf : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathSquareTargetMap_fst u v p q h 0
  apply pullback.hom_ext
  · rw [Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v) = _
    rw [hf]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u ≫
        (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q) = _
    rw [← Category.assoc]
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u = u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl X from
        pullback.lift_fst _ _ _, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalencePathRefl_map, ← Category.assoc, h]
    change (p ≫ v) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y =
      p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection v ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v)
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection v ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v = v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y from
        pullback.lift_fst _ _ _, Category.assoc]
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v =
      (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection v) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap_projection, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection, Category.id_comp, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection, Category.comp_id]

/-- 同時解像の両端の持ち上げにより、同値な span の実際の pullback 比較も同値。 -/
lemma isPrecompositionEquivalence_spanPullbackMap_of_equivalenceLifting
    {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    [Quasicategory A₀] [Quasicategory A₁] [Quasicategory A₂]
    [Quasicategory B₀] [Quasicategory B₁] [Quasicategory B₂]
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀)
    (hu₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence u₀) (hu₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence u₁) (hu₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence u₂)
    (hp₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p₁) (hq₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting q₁)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt q₁ 0)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂) := by
  let r₁ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u₁ u₀ p₁ q₁ h₁
  let r₂ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u₂ u₀ p₂ q₂ h₂
  have hs₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u₁ ≫ p₁ =
      r₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u₀ :=
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap_projection u₁ u₀ p₁ q₁ h₁).symm
  have hs₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u₂ ≫ p₂ =
      r₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u₀ :=
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap_projection u₂ u₀ p₂ q₂ h₂).symm
  have ht₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u₁ ≫ q₁ =
      r₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u₀ :=
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap_endpoint u₁ u₀ p₁ q₁ h₁).symm
  have ht₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u₂ ≫ q₂ =
      r₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u₀ :=
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap_endpoint u₂ u₀ p₂ q₂ h₂).symm
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap r₁ r₂ p₁ p₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u₂) hs₁ hs₂
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap r₁ r₂ q₁ q₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u₂) ht₁ ht₂
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration s :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_spanPullbackMap_of_left_corner r₁ r₂ p₁ p₂ _ _ _ hs₁ hs₂
      (replacementSquareStartCornerFlipped u₁ u₀ p₁ q₁ h₁)
      (replacementSquareStartCornerFlipped_fst u₁ u₀ p₁ q₁ h₁)
      (replacementSquareStartCornerFlipped_snd u₁ u₀ p₁ q₁ h₁)
  have := hu₂.equivalencePathReplacementMap_trivialKanFibration
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_replacementSquareEndCorner u₁ u₀ p₁ q₁ h₁ hu₁ hu₀ hp₁ hq₁
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration t :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.trivialKanFibration_spanPullbackMap_of_left_corner r₁ r₂ q₁ q₂ _ _ _ ht₁ ht₂
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner u₁ u₀ p₁ q₁ h₁)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner_fst u₁ u₀ p₁ q₁ h₁)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner_snd u₁ u₀ p₁ q₁ h₁)
  have hj₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u₁ ≫ r₁ =
      p₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u₀ :=
    replacementSquareMap_section u₁ u₀ p₁ q₁ h₁
  have hj₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u₂ ≫ r₂ =
      p₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u₀ :=
    replacementSquareMap_section u₂ u₀ p₂ q₂ h₂
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap p₁ p₂ r₁ r₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection u₂) hj₁ hj₂
  have hjs : j ≫ s = 𝟙 (pullback p₁ p₂) := by
    apply pullback.hom_ext
    · dsimp only [j, s]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_fst, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_fst,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection,
        Category.comp_id, Category.id_comp]
    · dsimp only [j, s]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_snd, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_snd,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection,
        Category.comp_id, Category.id_comp]
  have hjt : j ≫ t = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂ := by
    apply pullback.hom_ext
    · dsimp only [j, t]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_fst, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_fst,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_fst]
    · dsimp only [j, t]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_snd, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_snd,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_snd]
  have := hp₁.innerFibration
  have := hq₁.innerFibration
  have : InnerFibration (pullback.snd p₁ p₂) :=
    ⟨innerFibrations.pullback_snd _ _ (mem_innerFibrations p₁)⟩
  have : InnerFibration (pullback.snd q₁ q₂) :=
    ⟨innerFibrations.pullback_snd _ _ (mem_innerFibrations q₁)⟩
  have : Quasicategory (pullback p₁ p₂) := quasicategory_of_innerFibration (pullback.snd p₁ p₂)
  have : Quasicategory (pullback q₁ q₂) := quasicategory_of_innerFibration (pullback.snd q₁ q₂)
  have : Quasicategory (pullback r₁ r₂) := quasicategory_of_innerFibration s
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence j := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration s).cancel_right
    rw [hjs]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl _).isQCatEquivalence
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂) := by
    rw [← hjt]
    exact hj.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration t)
  exact he.isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
