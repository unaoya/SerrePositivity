module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RelativeRoofPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.RightFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.InitialDiagramSlice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft
/-!
概要：元の実屋根の left cofinal 比較から、引き戻し圏への実図式の left cofinality を導く。
方針：各 Quillen A の全 slice を右ファイブレーションへの基底変換として計算する。
規約：実屋根比較・全図式の始対象値・実添字の弱可縮性を使用。
使われ方：実逆分母から Drinfeld 商の右 Kan 形状への cofinality。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
variable {I E X Q : SSet.{u}} (r : E ⟶ Q) [InnerFibration r] (q : X ⟶ Q)
variable (u : I ⟶ pullback r q) (b : (Δ[0] : SSet.{u}) ⟶ pullback r q)
/-- 元の屋根比較が left cofinal なら、元の全 slice から商側三角形への射も left cofinal。 -/
lemma relativeRoofTriangleMap_isLeftCofinal
    (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison r q u b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofTriangleMap r q u b) := by
  let hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSquare_isPullback r q u b
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rightFibration_pullback_isLeftCofinal
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap r (u ≫ pullback.fst r q) (b ≫ pullback.fst r q))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison r q u b) hw
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_leftAnodyne hp.isoPullback.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.of_isIso hp.isoPullback.hom)
  have hc := he.comp h
  rw [hp.isoPullback_hom_fst] at hc
  exact hc
/-- 元の実屋根比較と始対象値図式から、元の同じ Quillen A の全 slice の弱可縮性を得る。 -/
lemma relativeRoofSlice_isWeaklyContractible [Quasicategory E]
    (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison r q u b))
    (ha : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((u ≫ pullback.fst r q).app (Opposite.op ⦋0⦌) i))
    (hI : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback u (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection b)) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.initialDiagramSlice_isWeaklyContractible (u ≫ pullback.fst r q) ha
    (SSet.yonedaEquiv (b ≫ pullback.fst r q)) hI
  have hp : SSet.yonedaEquiv.symm (SSet.yonedaEquiv (b ≫ pullback.fst r q)) =
      b ≫ pullback.fst r q := SSet.yonedaEquiv.symm_apply_apply _
  have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangle (u ≫ pullback.fst r q) (b ≫ pullback.fst r q)) :=
    (congrArg (fun t : (Δ[0] : SSet.{u}) ⟶ E => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible
      (pullback (u ≫ pullback.fst r q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection t))) hp).mp hc
  have he := (relativeRoofTriangleMap_isLeftCofinal r q u b hw).isWeakHomotopyEquivalence
  exact he.weaklyContractible_iff.mpr hc'
/-- 任意実屋根比較の cofinality は、始対象値の実図式から引き戻し圏への cofinality を与える。 -/
lemma isLeftCofinal_of_relativeRoofComparisons [Quasicategory E] [Quasicategory X]
    (hw : ∀ c : (pullback r q) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison r q u (SSet.yonedaEquiv.symm c)))
    (ha : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((u ≫ pullback.fst r q).app (Opposite.op ⦋0⦌) i))
    (hI : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible I) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal u := by
  have : InnerFibration (pullback.snd r q) :=
    ⟨innerFibrations.pullback_snd r q (InnerFibration.mem (q := r))⟩
  have : Quasicategory (pullback r q) := quasicategory_of_innerFibration (pullback.snd r q)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_weaklyContractible_slices
  intro c
  exact relativeRoofSlice_isWeaklyContractible r q u _ (hw c) ha hI
end SerrePositivity.InfinityCategories.Project.DerivedCategories
