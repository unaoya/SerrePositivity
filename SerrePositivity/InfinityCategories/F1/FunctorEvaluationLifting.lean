module

public import SerrePositivity.InfinityCategories.F1.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramRestrictionFibration

/-!
概要：頂点評価と、その両端固定の区間 Hom への作用の持ち上げ性。
方針：頂点の単射による前合成を、一点関手空間の同型で後合成する。
規約：始域に充填性は要求せず、標的のみ quasicategory とする。
使われ方：元の分類先の Hom の成分評価を Kan fibration として扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の頂点評価は、単射な同値に対する右持ち上げ性を持つ。 -/
lemma kanEquivalenceLifting_evaluateFunctorAt {B X : SSet.{u}} [Quasicategory X]
    (b : B _⦋0⦌) : F1B.KanEquivalenceLifting (evaluateFunctorAt (Y := X) b) := by
  let j : (Δ[0] : SSet.{u}) ⟶ B := SSet.yonedaEquiv.symm b
  haveI : Mono j := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro a b _
    apply stdSimplex.ext
    intro i
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  have hj : j.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) = b := by
    have hv : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply stdSimplex.ext
      intro i
      exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
    rw [hv]
    exact SSet.yonedaEquiv_symm_app_id b
  have he : (pre j).app X ≫ (pointFunctorEvaluationIso X).hom =
      evaluateFunctorAt (Y := X) b := by
    change (pre j).app X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
    rw [evaluateFunctorAt_pre, hj]
  rw [← he]
  intro A D i hi heq
  have : HasLiftingProperty i ((pre j).app X) := F1B.kanEquivalenceLifting_pre j i hi heq
  infer_instance

/-- 同じ頂点評価の両端固定の区間 Hom 上の作用は Kan fibration。 -/
lemma intervalMappingPostOfEq_evaluateFunctorAt_fibration
    {B X : SSet.{u}} [Quasicategory X] (b : B _⦋0⦌)
    (F G : ((ihom B).obj X) _⦋0⦌) {x y : X _⦋0⦌}
    (hx : (evaluateFunctorAt (Y := X) b).app _ F = x)
    (hy : (evaluateFunctorAt (Y := X) b).app _ G = y) :
    Fibration (intervalMappingPostOfEq (evaluateFunctorAt (Y := X) b) F G hx hy) :=
  intervalMappingPostOfEq_fibration _ (kanEquivalenceLifting_evaluateFunctorAt b) F G hx hy

end SerrePositivity.InfinityCategories
