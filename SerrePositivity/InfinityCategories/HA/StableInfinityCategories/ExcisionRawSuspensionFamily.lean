module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSuspensionEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionInitialReplacementPullback

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionRawSuspensionFamily {X : SSet.{u}} (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X :=
  curry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape ≫ F)

lemma excisionRawSuspensionFamily_source {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X) :
    excisionRawSuspensionFamily F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ F := by
  rw [excisionRawSuspensionFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.curry_evaluation_vertex]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionEvaluateShape 0 0 ≫ F = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionEvaluateShape_source]

lemma excisionRawSuspensionFamily_target {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X) :
    excisionRawSuspensionFamily F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) =
        (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFinalSquare ≫ F := by
  rw [excisionRawSuspensionFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.curry_evaluation_vertex]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionEvaluateShape 1 1 ≫ F = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionEvaluateShape_target, Category.assoc]

lemma excisionRawSuspensionFamily_replaced_source {X : SSet.{u}} [Quasicategory X]
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (excisionRawSuspensionFamily (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)) := by
  rw [excisionRawSuspensionFamily_source]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial_input_isPullback c hc

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
