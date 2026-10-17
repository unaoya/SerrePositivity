module
public import SerrePositivity.InfinityCategories.DGNerve.CospanPrefixReplacement
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra

/-! # 先頭置換後の脚側右辺の型付き検証

概要：先頭解が型付き Hom の脚の線形式を満たすなら、先頭を置換した脚側右辺は零。
方針：右辺の変化の公式を異種等号に沿って移し、型付き解の式を使う。
規約：HA Proposition 1.3.1.10。使われ方：実際の候補の脚側の方程式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：先頭に挿入する成分を有効な固定端点・次数で評価する。
方針：先頭集合の濃度と端点を指定する。
規約：HA Construction 1.3.1.6。使われ方：置換族と型付きの先頭解との比較。 -/
def cospanPrefixReplacementHom {n : ℕ} (s : SimplexData A D (n + 3))
    (f : ∀ a b k (hM : 2 ≤ (cospanPrefixFaces n).card),
      a = (cospanPrefixFaces n).min' (Index.nonempty hM) →
      b = (cospanPrefixFaces n).max' (Index.nonempty hM) →
      k = 2 - ((cospanPrefixFaces n).card : ℤ) → GradedHom A (s.obj a) (s.obj b) k) :
    GradedHom A (s.obj 0) (s.obj (cospanApex n)) (-(n : ℤ)) :=
  f 0 (cospanApex n) (-(n : ℤ)) (by rw [card_cospanPrefixFaces]; omega)
    (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
    (by rw [card_cospanPrefixFaces]; push_cast; omega)

/-- 概要：先頭解の射影の線形式が成り立つなら、先頭成分を挿入した脚側右辺は零。
方針：生の右辺の変化の式を固定した Hom へ移し、射影と残差の和が零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：未知脚成分を零にした方程式の右辺を消去する。 -/
lemma cospanOneTailRhs_replace_prefix_zero_of_heq {n : ℕ} (s : SimplexData A D (n + 3))
    (f : ∀ a b k (hM : 2 ≤ (cospanPrefixFaces n).card),
      a = (cospanPrefixFaces n).min' (Index.nonempty hM) →
      b = (cospanPrefixFaces n).max' (Index.nonempty hM) →
      k = 2 - ((cospanPrefixFaces n).card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (hzero : s.cospanPrefixHom = 0) (b : Fin (n + 4)) (hb : cospanApex n < b)
    {X P Y : D} (hx : s.obj 0 = X) (hP : s.obj (cospanApex n) = P) (hy : s.obj b = Y)
    {l : ℤ} (hl : -(n : ℤ) - 1 + 1 = l)
    (a : GradedHom A X P l) (r : GradedHom A X Y l) (p : GradedHom A P Y 0)
    (ha : HEq (s.cospanPrefixReplacementHom f) a) (hr : HEq (s.cospanOneTailRhs b hb) r)
    (hp : HEq (s.edgeHom (cospanApex n) b hb) p)
    (hsolve : r + compose A p a (add_zero l) = 0) :
    (s.replace (cospanPrefixFaces n) f).cospanOneTailRhs b hb = 0 := by
  have H := s.cospanOneTailRhs_replace_prefix f b hb
  change _ - _ = compose A _ (s.cospanPrefixReplacementHom f - s.cospanPrefixHom) _ at H
  rw [hzero, sub_zero] at H
  have hdeg : -(n : ℤ) = l := by omega
  have hc := gradedHom_compose_heq (A := A) hx hP hy hdeg rfl hl
    _ _ p a hp ha (by omega) (add_zero l)
  have hs := gradedHom_add_heq (A := A) hx hy hl _ _ _ _ hr hc
  have hval := (sub_eq_iff_eq_add.mp H).trans (add_comm _ _)
  have ht := (heq_of_eq hval).trans (hs.trans (heq_of_eq hsolve))
  exact eq_of_heq (ht.trans (gradedHom_zero_heq (A := A) hx hy hl).symm)

/-- 概要：先頭成分を挿入した脚側右辺は、元の右辺と射影との合成の和へ異種等号で移る。
方針：生の右辺の変化の式を固定した Hom へ移す。
規約：HA Proposition 1.3.1.10。使われ方：非零の D 側成分の微分方程式の右辺を同定する。 -/
lemma cospanOneTailRhs_replace_prefix_heq {n : ℕ} (s : SimplexData A D (n + 3))
    (f : ∀ a b k (hM : 2 ≤ (cospanPrefixFaces n).card),
      a = (cospanPrefixFaces n).min' (Index.nonempty hM) →
      b = (cospanPrefixFaces n).max' (Index.nonempty hM) →
      k = 2 - ((cospanPrefixFaces n).card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (hzero : s.cospanPrefixHom = 0) (b : Fin (n + 4)) (hb : cospanApex n < b)
    {X P Y : D} (hx : s.obj 0 = X) (hP : s.obj (cospanApex n) = P) (hy : s.obj b = Y)
    {l : ℤ} (hl : -(n : ℤ) - 1 + 1 = l)
    (a : GradedHom A X P l) (r : GradedHom A X Y l) (p : GradedHom A P Y 0)
    (ha : HEq (s.cospanPrefixReplacementHom f) a) (hr : HEq (s.cospanOneTailRhs b hb) r)
    (hp : HEq (s.edgeHom (cospanApex n) b hb) p) :
    HEq ((s.replace (cospanPrefixFaces n) f).cospanOneTailRhs b hb)
      (r + compose A p a (add_zero l)) := by
  have H := s.cospanOneTailRhs_replace_prefix f b hb
  change _ - _ = compose A _ (s.cospanPrefixReplacementHom f - s.cospanPrefixHom) _ at H
  rw [hzero, sub_zero] at H
  have hdeg : -(n : ℤ) = l := by omega
  have hc := gradedHom_compose_heq (A := A) hx hP hy hdeg rfl hl
    _ _ p a hp ha (by omega) (add_zero l)
  have hs := gradedHom_add_heq (A := A) hx hy hl _ _ _ _ hr hc
  have hval := (sub_eq_iff_eq_add.mp H).trans (add_comm _ _)
  exact (heq_of_eq hval).trans hs

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
