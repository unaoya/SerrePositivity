module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictCoherentFamily

/-!
概要：元の有限射列と HA 単体の全厳密成分から、対角の HA 単体を構成する。
方針：閉零成分を後合成し、切断位置で全高次成分の自然性と合成則を使う。
規約：各部分集合の元の HA 成分と全次数の方程式を保つ。
使われ方：3b-3 R6、元の指定余錐を全パラメーターの射列と同時に評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace OrderedSimplexFamily
variable {A : Type u} [CommRing A] {E : Type v} [DGCategory A E] {n : ℕ}
  (d : OrderedSimplexFamily A E n)

/-- 元の閉零成分を、元の斉次射に後合成する。 -/
def transport (p q : Fin (n + 1)) (hpq : p ≤ q) {a b : Fin (n + 1)} {k : ℤ}
    (f : GradedHom A ((d.obj p).obj a) ((d.obj p).obj b) k) :
    GradedHom A ((d.obj p).obj a) ((d.obj q).obj b) k :=
  compose A ((d.map p q hpq).app b).val f (add_zero k)

/-- 元の閉零後合成は零を保つ。 -/
lemma transport_zero (p q : Fin (n + 1)) (hpq : p ≤ q) (a b : Fin (n + 1)) (k : ℤ) :
    d.transport p q hpq (0 : GradedHom A ((d.obj p).obj a) ((d.obj p).obj b) k) = 0 :=
  compose_zero _ _

/-- 元の閉零後合成は差を保つ。 -/
lemma transport_sub (p q : Fin (n + 1)) (hpq : p ≤ q) {a b : Fin (n + 1)} {k : ℤ}
    (f g : GradedHom A ((d.obj p).obj a) ((d.obj p).obj b) k) :
    d.transport p q hpq (f - g) = d.transport p q hpq f - d.transport p q hpq g :=
  compose_sub_right _ _ _ _

/-- 元の閉零後合成は符号のスカラー倍を保つ。 -/
lemma transport_smul (p q : Fin (n + 1)) (hpq : p ≤ q) {a b : Fin (n + 1)} {k : ℤ}
    (c : ℤˣ) (f : GradedHom A ((d.obj p).obj a) ((d.obj p).obj b) k) :
    d.transport p q hpq (c • f) = c • d.transport p q hpq f :=
  compose_units_smul_right _ _ _ _

/-- 元の閉零後合成は有限和を保つ。 -/
lemma transport_sum {ι : Type*} (p q : Fin (n + 1)) (hpq : p ≤ q)
    {a b : Fin (n + 1)} {k : ℤ} (S : Finset ι)
    (f : ι → GradedHom A ((d.obj p).obj a) ((d.obj p).obj b) k) :
    d.transport p q hpq (∑ i ∈ S, f i) = ∑ i ∈ S, d.transport p q hpq (f i) :=
  compose_sum_right _ _ _ _

/-- 元の閉零後合成は全次数の微分と可換する。 -/
lemma transport_differential (p q : Fin (n + 1)) (hpq : p ≤ q)
    {a b : Fin (n + 1)} {k : ℤ}
    (f : GradedHom A ((d.obj p).obj a) ((d.obj p).obj b) k) :
    differential A (d.transport p q hpq f) = d.transport p q hpq (differential A f) := by
  unfold transport
  have hc : differential A ((d.map p q hpq).app b).val = 0 := (d.map p q hpq).app b |>.property
  rw [differential_compose]
  simp only [hc, zero_compose, Int.negOnePow_zero, one_smul, zero_add]

/-- 三位置の閉零後合成は、元の高次成分との可換式に沿って切断できる。 -/
lemma transport_compose (p q r : Fin (n + 1)) (hpq : p ≤ q) (hqr : q ≤ r)
    {a b c : Fin (n + 1)} {i j k : ℤ}
    (g : GradedHom A ((d.obj p).obj b) ((d.obj p).obj c) j)
    (g' : GradedHom A ((d.obj q).obj b) ((d.obj q).obj c) j)
    (hg : compose A ((d.map p q hpq).app c).val g (add_zero j) =
      compose A g' ((d.map p q hpq).app b).val (zero_add j))
    (f : GradedHom A ((d.obj p).obj a) ((d.obj p).obj b) i) (hk : i + j = k) :
    d.transport p r (hpq.trans hqr) (compose A g f hk) =
      compose A (d.transport q r hqr g') (d.transport p q hpq f) hk := by
  have hc := congrArg (fun m : StrictSimplexMap A E (d.obj p).toSimplexData
      (d.obj r).toSimplexData => (m.app c).val) (d.map_trans p q r hpq hqr)
  change compose A ((d.map q r hqr).app c).val ((d.map p q hpq).app c).val
    (zero_add 0) = ((d.map p r (hpq.trans hqr)).app c).val at hc
  unfold transport
  rw [← hc]
  calc
    _ = compose A ((d.map q r hqr).app c).val
        (compose A ((d.map p q hpq).app c).val (compose A g f hk) (add_zero k))
        (add_zero k) :=
      (NestedCut.compose_assoc_of_sum _ _ _ (add_zero k) (zero_add 0) (add_zero k)).symm
    _ = compose A ((d.map q r hqr).app c).val
        (compose A (compose A ((d.map p q hpq).app c).val g (add_zero j)) f hk)
        (add_zero k) := by rw [NestedCut.compose_assoc_of_sum _ _ _ hk (add_zero j) (add_zero k)]
    _ = compose A ((d.map q r hqr).app c).val
        (compose A (compose A g' ((d.map p q hpq).app b).val (zero_add j)) f hk)
        (add_zero k) := by rw [hg]
    _ = compose A ((d.map q r hqr).app c).val
        (compose A g' (compose A ((d.map p q hpq).app b).val f (add_zero i)) hk)
        (add_zero k) := by
      rw [← NestedCut.compose_assoc_of_sum _ _ _ (add_zero i) (zero_add j) hk]
    _ = _ := NestedCut.compose_assoc_of_sum _ _ _ hk (add_zero j) (add_zero k)

/-- 同じ有限射列の対角で、元の HA 成分を閉零射に後合成した単体データ。 -/
def diagonalData : SimplexData A E n where
  obj a := (d.obj a).obj a
  hom I a b k hI ha hb hk := d.transport a b (by
    rw [ha, hb]
    exact (I.isLeast_min' _).2 (I.max'_mem _)) ((d.obj a).hom I a b k hI ha hb hk)

/-- 対角の各内部点の寄与は、元の同じ符号・削除・切断成分の像。 -/
lemma diagonalData_term (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hab : a ≤ b) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    d.transport a b hab ((d.obj a).toSimplexData.term I a b k hI ha hb hk j hj haj hjb) =
      d.diagonalData.term I a b k hI ha hb hk j hj haj hjb := by
  simp only [SimplexData.term, diagonalData, transport_smul, transport_sub]
  congr 2
  exact d.transport_compose a j b haj.le hjb.le _ _
    ((d.map a j haj.le).naturality _ _ _ _ _ _ _ _) _ _

/-- 対角の方程式の右辺は、元の同じ全内部点の和の像。 -/
lemma diagonalData_rhs (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) (hab : a ≤ b) :
    d.transport a b hab ((d.obj a).toSimplexData.rhs I a b k hI ha hb hk) =
      d.diagonalData.rhs I a b k hI ha hb hk := by
  unfold SimplexData.rhs
  rw [transport_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hj]
    exact d.diagonalData_term I a b k hI ha hb hk hab j.val j.property hj.1 hj.2
  · simp only [dite_eq_right hj, transport_zero]

/-- 同じ有限射列と全 HA 成分を使う対角の実単体。 -/
def diagonal : Simplex A E n where
  toSimplexData := d.diagonalData
  equation I a b k hI ha hb hk := by
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (I.isLeast_min' _).2 (I.max'_mem _)
    change differential A (d.transport a b hab ((d.obj a).hom I a b k hI ha hb hk)) = _
    rw [transport_differential, (d.obj a).equation, diagonalData_rhs]


end OrderedSimplexFamily
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
