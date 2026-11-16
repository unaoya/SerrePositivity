module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeRestrictionCocartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import Mathlib.Data.Fin.Basic

/-!
概要：全錐の関手空間の頂点評価は、同じjoin錐の頂点を返す。
方針：Yoneda同値の後合成則で、同じ一点での評価を表示する。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存評価の計算法則。
使われ方：S8 の同じ指定右Kan輸送の頂点の型の移送。
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 元の全錐の評価関手を同じ錐で評価した頂点等式。 -/
lemma coneApexEvaluation_vertex {K X : SSet.{u}} {p : K ⟶ X} (d : JoinCone p) :
    (coneApexEvaluation K X).app _ (functorVertex d.val) = d.vertex := by
  rw [coneApexEvaluation,
    SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex,
    JoinCone.vertex_eq, SSet.yonedaEquiv_comp]
  congr 1
  have h := SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u}))
    (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K)
  have h0 : SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) =
      stdSimplex.obj₀Equiv.symm (0 : Fin 1) := stdSimplex.obj₀Equiv.injective ((Fin.eq_zero _).trans (Fin.eq_zero _).symm)
  simpa only [Category.id_comp, h0] using h.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
