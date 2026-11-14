module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGNerveBasic
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut

/-! # dg nerve 単体の始点への前合成

概要：閉次数零射を単体の始点に前合成し、新しい単体を作る。
方針：始点から出る全 cochain に前合成し、微分と切断合成の方程式を移す。
規約：任意の dg 圏・全次数。使われ方：D7 の錐比較三単体。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
set_option backward.isDefEq.respectTransparency false
universe u v
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
namespace SourcePrecomposition
variable {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) {X : D}
  (f : _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject R D X (s.obj 0)))
/-- 最初の頂点だけを新しい始域に置き換える。 -/
def obj : Fin (n + 1) → D := Fin.cases X (fun i => s.obj i.succ)
/-- 始点から出る cochain に閉次数零射を前合成する。 -/
def hom : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily R D (obj s (X := X)) := by
  intro I a b k hI ha hb hk
  have hab : a < b := by
    rw [ha, hb]
    exact I.min'_lt_max'_of_card hI
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => exact False.elim (by simp at hab)
    | succ b => exact compose R (s.hom I 0 b.succ k hI ha hb hk) f.val (zero_add k)
  | succ a =>
    cases b using Fin.cases with
    | zero => exact False.elim (by simp at hab)
    | succ b => exact s.hom I a.succ b.succ k hI ha hb hk

/-- 始点と cochain を同時に置き換えた単体データ。 -/
def data : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n where
  obj := obj s (X := X)
  hom := hom s f

/-- 始点から出る成分の評価。 -/
lemma hom_zero (I : Finset (Fin (n + 1))) (b : Fin n) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : (0 : Fin (n + 1)) = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b.succ = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    (data s f).hom I 0 b.succ k hI ha hb hk =
      _root_.SerrePositivity.DifferentialGraded.compose R (s.hom I 0 b.succ k hI ha hb hk) f.val (zero_add k) := rfl

/-- 始点を含まない成分は元の成分。 -/
lemma hom_succ (I : Finset (Fin (n + 1))) (a b : Fin n) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a.succ = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b.succ = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    (data s f).hom I a.succ b.succ k hI ha hb hk =
      s.hom I a.succ b.succ k hI ha hb hk := rfl
/-- 始点を含まない切断寄与は変わらない。 -/
lemma term_succ (I : Finset (Fin (n + 1))) (a b : Fin n) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a.succ = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b.succ = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a.succ < j) (hjb : j < b.succ) :
    (data s f).term I a.succ b.succ k hI ha hb hk j hj haj hjb =
      s.term I a.succ b.succ k hI ha hb hk j hj haj hjb := by
  cases j using Fin.cases with
  | zero => simp at haj
  | succ j => simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.hom_succ]

/-- 始点を含む切断寄与には閉射が一度だけ前合成される。 -/
lemma term_zero (I : Finset (Fin (n + 1))) (b : Fin n) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : (0 : Fin (n + 1)) = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b.succ = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : 0 < j) (hjb : j < b.succ) :
    (data s f).term I 0 b.succ k hI ha hb hk j hj haj hjb =
      _root_.SerrePositivity.DifferentialGraded.compose R (s.term I 0 b.succ k hI ha hb hk j hj haj hjb) f.val (zero_add (k + 1)) := by
  cases j using Fin.cases with
  | zero => simp at haj
  | succ j =>
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.hom_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.hom_succ,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum]
/-- 始点を含まない方程式の右辺は変わらない。 -/
lemma rhs_succ (I : Finset (Fin (n + 1))) (a b : Fin n) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a.succ = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b.succ = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    (data s f).rhs I a.succ b.succ k hI ha hb hk =
      s.rhs I a.succ b.succ k hI ha hb hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · exact term_succ s f I a b k hI ha hb hk j.val j.property h.1 h.2
  · rfl

/-- 始点を含む方程式の右辺は前合成の像。 -/
lemma rhs_zero (I : Finset (Fin (n + 1))) (b : Fin n) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : (0 : Fin (n + 1)) = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b.succ = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    (data s f).rhs I 0 b.succ k hI ha hb hk =
      _root_.SerrePositivity.DifferentialGraded.compose R (s.rhs I 0 b.succ k hI ha hb hk) f.val (zero_add (k + 1)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · exact term_zero s f I b k hI ha hb hk j.val j.property h.1 h.2
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose _ _).symm

/-- 閉次数零射による前合成は微分と可換。 -/
lemma differential_precompose {Z : D} {k : ℤ} (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj 0) Z k) :
    _root_.SerrePositivity.DifferentialGraded.differential R (compose R h f.val (zero_add k)) =
      _root_.SerrePositivity.DifferentialGraded.compose R (differential R h) f.val (zero_add (k + 1)) := by
  rw [_root_.SerrePositivity.DifferentialGraded.differential_compose]
  have hf : differential R f.val = 0 := f.property
  rw [hf, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]

variable (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n) {Y : D}
  (g : _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject R D Y (σ.obj 0)))
/-- 始点に閉次数零射を前合成した実際の dg nerve 単体。 -/
def simplex : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n where
  toSimplexData := data σ.toSimplexData g
  equation I a b k hI ha hb hk := by
    have hab : a < b := by
      rw [ha, hb]
      exact I.min'_lt_max'_of_card hI
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => simp at hab
      | succ b =>
        calc
          _ = compose R (differential R (σ.hom I 0 b.succ k hI ha hb hk)) g.val
              (zero_add (k + 1)) := differential_precompose σ.toSimplexData g _
          _ = compose R (σ.toSimplexData.rhs I 0 b.succ k hI ha hb hk) g.val
              (zero_add (k + 1)) := congrArg (fun z => compose R z g.val (zero_add (k + 1)))
                (σ.equation I 0 b.succ k hI ha hb hk)
          _ = _ := (rhs_zero σ.toSimplexData g I b k hI ha hb hk).symm
    | succ a =>
      cases b using Fin.cases with
      | zero => simp at hab
      | succ b =>
        exact (σ.equation I a.succ b.succ k hI ha hb hk).trans
          (rhs_succ σ.toSimplexData g I a b k hI ha hb hk).symm
end SourcePrecomposition

end SerrePositivity.InfinityCategories.Project.DerivedCategories
