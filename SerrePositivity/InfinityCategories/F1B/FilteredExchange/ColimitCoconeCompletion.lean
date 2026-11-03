module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.F1B.Cones.RelativeInitialCoconeVertex
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeColimit
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialBoundaryCriterion
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialColimitFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.FunctorCoconePointwiseCriterion
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.Core.CoconeFamily
public import SerrePositivity.InfinityCategories.F1.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Core.RelativeInitialBoundary
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone

/-!
概要：余極限全余錐族の点ごとの余極限補完は、再び余極限全余錐となる。
方針：全族の後合成の相対始対象性を、同じ完成後の右端で反映する。
規約：二つの元の添字と全余錐を保ち、filtered 性や有限性を仮定しない。
使われ方：Ind の有限余極限の全錐族の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 余錐形状の関手頂点を同じ全余錐へ読み戻す。 -/
def functorVertexCocone {K X : SSet.{u}}
    (v : ((ihom (join K (Δ[0] : SSet.{u}))).obj X) _⦋0⦌) :
    JoinCocone (joinInl K Δ[0] ≫ (functorVertexEquiv _ _).symm v) :=
  ⟨(functorVertexEquiv _ _).symm v, rfl⟩

/-- 余極限全余錐族の点ごとの余極限補完は、その同じ最終余錐で余極限となる。 -/
lemma colimitCoconeFamily_completion_isColimit {I K X : SSet.{u}} [Quasicategory X]
    (p : I ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj X) (c : JoinCocone p)
    (hc : IsPointwiseColimitCone c)
    (hp : ∀ i : I _⦋0⦌, IsColimitCone (functorVertexCocone (p.app (Opposite.op ⦋0⦌) i))) :
    IsColimitCone (functorVertexCocone c.vertex) := by
  let U := coconeRestriction K X
  have hrows (i : I _⦋0⦌) : InitialBoundaryLifting U (p.app (Opposite.op ⦋0⦌) i) := by
    have h := (hp i).initialBoundaryLifting
    have hv : functorVertex (functorVertexCocone (p.app (Opposite.op ⦋0⦌) i)).val =
        p.app (Opposite.op ⦋0⦌) i := (functorVertexEquiv _ _).apply_symm_apply _
    rw [hv] at h
    exact h
  have hcol : IsColimitCone c := isColimitCone_functor_of_pointwise c hc
  have him : IsColimitCone (mapJoinCocone U c) :=
    isColimitCone_functor_of_pointwise _ (hc.reindex (joinInl K Δ[0]))
  have hg := F1B.relativeInitial_colimitCoconeFamily U p hrows c hcol him
  have ht := F1B.relativeInitial_cocone_vertex U c hg
  have hb := F1B.kanInitialBoundaryLifting_of_relativeInitial U c.vertex ht
  have hv : functorVertex (functorVertexCocone c.vertex).val = c.vertex :=
    (functorVertexEquiv _ _).apply_symm_apply _
  rw [← hv] at hb
  exact isColimitCone_of_initialBoundaryLifting_coconeRestriction _ hb

end SerrePositivity.InfinityCategories.F2
