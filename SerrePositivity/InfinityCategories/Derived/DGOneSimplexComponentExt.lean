module
public import SerrePositivity.InfinityCategories.DGNerve.LowDimensional

/-! # dg nerve の一単体の型付き成分比較

概要：両対象の等式と唯一の閉零成分の異種等式から、一単体の厳密等式を得る。
方針：一単体の辺同値に渡し、対象の移送を閉零 cycle の外延性で処理する。
規約：対象族の等式による移送を省略しない。使われ方：回収した閉辺の実一次単体の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 閉零 cycle は、両対象の等式と台の異種等式で型付きに比較できる。 -/
lemma dgZeroCycle_heq {x y x' y' : D} (hx : x = x') (hy : y = y')
    (f : zeroCycles (homObject A D x y)) (g : zeroCycles (homObject A D x' y'))
    (h : HEq f.val g.val) : HEq f g := by
  cases hx
  cases hy
  exact heq_of_eq (Subtype.ext (eq_of_heq h))

/-- 一単体の両対象と唯一の斉次成分の一致から、実一次単体の厳密等式を得る。 -/
lemma dgOneSimplex_ext {s t : Simplex A D 1} (h₀ : s.obj 0 = t.obj 0)
    (h₁ : s.obj 1 = t.obj 1)
    (hf : HEq (s.edgeHom 0 1 (by decide)) (t.edgeHom 0 1 (by decide))) : s = t := by
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext (funext fun i => ?_) ?_
  · fin_cases i
    · exact h₀
    · exact h₁
  · exact dgZeroCycle_heq h₀ h₁ (s.edgeCycle 0 1 (by decide))
      (t.edgeCycle 0 1 (by decide)) hf

end SerrePositivity.InfinityCategories
