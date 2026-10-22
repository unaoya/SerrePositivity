module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSuspensionEvaluation
public import SerrePositivity.InfinityCategories.Stable.ExcisionInitialReplacementPullback

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
namespace SerrePositivity.InfinityCategories

def excisionRawSuspensionFamily {X : SSet.{u}} (F : nerve ExcisionGridIndex.{u} ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X :=
  curry (excisionGridSuspensionShape ≫ F)

lemma excisionRawSuspensionFamily_source {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X) :
    excisionRawSuspensionFamily F ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) =
        excisionGridSquareEmbedding ≫ F := by
  rw [excisionRawSuspensionFamily, curry_evaluation_vertex]
  change excisionGridSuspensionEvaluateShape 0 0 ≫ F = _
  rw [excisionGridSuspensionEvaluateShape_source]

lemma excisionRawSuspensionFamily_target {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X) :
    excisionRawSuspensionFamily F ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) =
        (β_ Δ[1] Δ[1]).hom ≫ excisionGridFinalSquare ≫ F := by
  rw [excisionRawSuspensionFamily, curry_evaluation_vertex]
  change excisionGridSuspensionEvaluateShape 1 1 ≫ F = _
  rw [excisionGridSuspensionEvaluateShape_target, Category.assoc]

lemma excisionRawSuspensionFamily_replaced_source {X : SSet.{u}} [Quasicategory X]
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (hc : IsLimitCone c) :
    IsPullbackSquare (excisionRawSuspensionFamily (excisionReplaceInitial c) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)) := by
  rw [excisionRawSuspensionFamily_source]
  exact excisionReplaceInitial_input_isPullback c hc

end SerrePositivity.InfinityCategories
