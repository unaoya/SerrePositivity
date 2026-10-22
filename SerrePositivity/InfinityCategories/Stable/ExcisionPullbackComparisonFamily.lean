module
public import SerrePositivity.InfinityCategories.Stable.ExcisionRawSuspensionSquare
public import SerrePositivity.InfinityCategories.Stable.FunctorPullbackComparisonEvaluation

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

def excisionPullbackComparisonFamily {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (d : JoinCone (pullbackCospan (excisionRawSuspensionSquare (excisionReplaceInitial c))))
    (hd : IsLimitCone d) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  functorPullbackComparisonFamily
    (excisionRawSuspensionSquare (excisionReplaceInitial c)) d hd

lemma excisionPullbackComparisonFamily_source {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (d : JoinCone (pullbackCospan (excisionRawSuspensionSquare (excisionReplaceInitial c))))
    (hd : IsLimitCone d) :
    excisionPullbackComparisonFamily c d hd ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
        excisionGridSquareEmbedding ≫ excisionReplaceInitial c := by
  rw [excisionPullbackComparisonFamily, functorPullbackComparisonFamily_source,
    excisionRawSuspensionSquare_source_vertex]
  exact (functorVertexEquiv _ _).symm_apply_apply _

lemma excisionPullbackComparisonFamily_source_isPullback {X : SSet.{u}} [Quasicategory X]
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (hc : IsLimitCone c)
    (d : JoinCone (pullbackCospan (excisionRawSuspensionSquare (excisionReplaceInitial c))))
    (hd : IsLimitCone d) :
    IsPullbackSquare (excisionPullbackComparisonFamily c d hd ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) := by
  rw [excisionPullbackComparisonFamily_source]
  exact excisionReplaceInitial_input_isPullback c hc

end SerrePositivity.InfinityCategories
