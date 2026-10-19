module
public import SerrePositivity.InfinityCategories.Derived.PinchedNormalizedBoundaryRhs

/-! # 指定最上位原始元による正規化した差の充填

概要：最上位比較の差を零面に置いた境界を、指定原始元の符号倍で充填する。
方針：実境界の全真部分集合の方程式と、最上位右辺の一項計算を接続する。
規約：最上位の次数を明示して cast を局所化する。使われ方：正次元の実相対比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 同じ最上位次数を別の整数で指定して充填する。 -/
def pinchedCompleteTopAtDegree {n : ℕ} (f : LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      differential A (f.component J k hJ hk) = f.rhs J k hk)
    (k : ℤ) (hk : k = pinchedTopDegree n) (h : GradedHom A x y k)
    (hh : differential A h = f.rhs Finset.univ k hk) : LinearSimplex A x y n := by
  subst hk
  exact pinchedCompleteTop f he h hh

/-- 指定次数による最上位置換も、全真部分集合を厳密に保つ。 -/
lemma pinchedCompleteTopAtDegree_proper {n : ℕ} (f : LinearData A x y n) (he)
    (k : ℤ) (hk : k = pinchedTopDegree n) (h : GradedHom A x y k) (hh)
    (J : Finset (Fin (n + 1))) (l : ℤ) (hJ : J.Nonempty) (hl : l = 1 - (J.card : ℤ))
    (hne : J ≠ Finset.univ) :
    (pinchedCompleteTopAtDegree f he k hk h hh).val.component J l hJ hl =
      f.component J l hJ hl := by
  subst hk
  exact pinchedCompleteTopData_proper f h J l hJ hl hne

/-- 指定次数での最上位成分は、指定原始元そのもの。 -/
lemma pinchedCompleteTopAtDegree_full {n : ℕ} (f : LinearData A x y n) (he)
    (k : ℤ) (hk : k = pinchedTopDegree n) (h : GradedHom A x y k) (hh) :
    (pinchedCompleteTopAtDegree f he k hk h hh).val.component Finset.univ k
      Finset.univ_nonempty hk = h := by
  subst hk
  exact pinchedCompleteTopData_full f h

/-- 指定終次数への微分式を、同じ成分の通常の cochain 微分へ戻す。 -/
lemma pinchedPrimitive_component_differential {n : ℕ} (f : LinearData A x y n)
    (p q : ℤ) (hpq : p + 1 = q)
    (hq : q = 1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ))
    (e : GradedHom A x y p)
    (he : (homObject A D x y).d p q e = f.component Finset.univ q Finset.univ_nonempty hq) :
    differential A e = f.component Finset.univ (p + 1) Finset.univ_nonempty (hpq.trans hq) := by
  subst hpq
  exact he

/-- 正規化した差の境界の右辺を指定原始元の符号倍で解く。 -/
lemma PinchedTopComparison.normalized_primitive_equation {n : ℕ}
    {s t : LinearSimplex A x y (n + 1)} (c : PinchedTopComparison s t) :
    differential A (deletionSign (Finset.univ : Finset (Fin (n + 3))) 0 • c.primitive) =
      (pinchedBoundaryKnownData (pinchedNormalizedBoundary (s - t) c.difference_proper_zero)).rhs
        Finset.univ (pinchedTopDegree (n + 1) - 1) (by simp [pinchedTopDegree]; omega) := by
  rw [pinchedNormalizedBoundary_rhs]
  rw [differential_units_smul]
  apply congrArg (fun a => deletionSign (Finset.univ : Finset (Fin (n + 3))) 0 • a)
  exact pinchedPrimitive_component_differential (s - t).val
    (pinchedTopDegree (n + 1) - 1) (pinchedTopDegree (n + 1)) (by omega) rfl c.primitive
      c.difference_full

/-- 指定原始元を使い、零面が差で他の面が零となる一段高い線形単体を作る。 -/
def PinchedTopComparison.normalizedFiller {n : ℕ} {s t : LinearSimplex A x y (n + 1)}
    (c : PinchedTopComparison s t) : LinearSimplex A x y (n + 2) :=
  pinchedCompleteTopAtDegree
    (pinchedBoundaryKnownData (pinchedNormalizedBoundary (s - t) c.difference_proper_zero))
    (pinchedBoundaryKnownData_equation _) (pinchedTopDegree (n + 1) - 1)
    (by simp [pinchedTopDegree]; omega)
    (deletionSign (Finset.univ : Finset (Fin (n + 3))) 0 • c.primitive)
    c.normalized_primitive_equation

end SerrePositivity.InfinityCategories
