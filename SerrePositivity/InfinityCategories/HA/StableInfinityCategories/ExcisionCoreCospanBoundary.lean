module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanHornIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionCoreCospanBoundary : (horn 2 2 : SSet.{u}) ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePuncturedIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanHornIso.hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCoreCospan)

lemma excisionCoreCospanBoundary_leftAnodyne :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions excisionCoreCospanBoundary.{u} := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCoreCospan.{u})) := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso_hom_ι]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.comp_mem _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.of_isIso _) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospan_leftAnodyne
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.of_isIso _) h

lemma excisionCoreCospanBoundary_mono : Mono excisionCoreCospanBoundary.{u} :=
  by
    unfold excisionCoreCospanBoundary
    infer_instance

lemma excisionCoreCospanBoundary_projection :
    excisionCoreCospanBoundary.{u} ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram 2 2 := by
  apply horn₂₂.isPushout.hom_ext
  · simp only [excisionCoreCospanBoundary, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanHornIso,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn_first,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;>
      apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide
  · simp only [excisionCoreCospanBoundary, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanHornIso,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn_second,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;>
      apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionCoreCospanBoundary_limit_iff {X : SSet.{u}} [Quasicategory X]
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePuncturedIndex.{u} ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c excisionCoreCospanBoundary) := by
  let := excisionCoreCospanBoundary_mono.{u}
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isLimitCone_iff_restrict_of_leftAnodyne c _
    excisionCoreCospanBoundary_leftAnodyne

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
