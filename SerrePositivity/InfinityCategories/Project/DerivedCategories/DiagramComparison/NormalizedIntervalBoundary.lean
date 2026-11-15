module
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic.FinCases
/-!
概要：指定区間への鎖写像を構成するための低次数境界の値。
方針：単調な二頂点への写像の有限場合分け。規約：A06の証明の分割。
-/
@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
/-- 区間の二つの頂点での値。 -/
def intervalVertexValue (x y : N) (i : Fin 2) : N := if i = 0 then x else y
/-- 非退化な辺にのみ指定した値を与える。 -/
def intervalEdgeValue (w : M) (i j : Fin 2) : M := if i = 0 ∧ j = 1 then w else 0
/-- 二頂点の境界は非退化な辺の場合だけ終点と始点の差になる。 -/
theorem interval_vertex_boundary (x y : N) (i j : Fin 2) (hij : i ≤ j) :
    intervalVertexValue x y j - intervalVertexValue x y i =
      if i = 0 ∧ j = 1 then y - x else 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [intervalVertexValue]
/-- 一次の鎖写像条件に使う同じ微分の値。 -/
theorem interval_edge_boundary (d : M →+ N) (x y : N) (w : M) (hw : d w = y - x)
    (i j : Fin 2) (hij : i ≤ j) :
    d (intervalEdgeValue w i j) = intervalVertexValue x y j - intervalVertexValue x y i := by
  rw [interval_vertex_boundary x y i j hij]
  by_cases h : i = 0 ∧ j = 1 <;> simp [intervalEdgeValue, h, hw]
/-- 二次境界の三辺の交代和は零。高次の成分を零にする際の条件。 -/
theorem interval_triangle_boundary (w : M) (f : Fin 3 →o Fin 2) :
    intervalEdgeValue w (f 1) (f 2) - intervalEdgeValue w (f 0) (f 2) +
      intervalEdgeValue w (f 0) (f 1) = 0 := by
  have h01 := f.monotone (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := f.monotone (show (1 : Fin 3) ≤ 2 by decide)
  generalize ha : f 0 = a at *
  generalize hb : f 1 = b at *
  generalize hc : f 2 = c at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [intervalEdgeValue]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
