module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MixedBoundary

/-! # 二重切断の合成値の一致

概要：二つの切断点による三重合成を、左右の切断順によらず同じ射へそろえる。
方針：四つの切断集合と中間次数を同定し、通常順合成の結合律を使う。
規約：HA Proposition 1.3.1.10。使われ方：実際の三重合成項を二重切断の符号相殺へ接続する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：中間の和次数を別名で指定した通常順合成の結合律。
方針：中間次数の等式を消去し、既存の結合律を適用する。
規約：HA Proposition 1.3.1.10。使われ方：二重切断の異なる中間次数の同定。 -/
lemma compose_assoc_of_sum {w x y z : D} {p q r a b t : ℤ}
    (f : GradedHom A w x p) (g : GradedHom A x y q) (h : GradedHom A y z r)
    (ha : p + q = a) (hb : q + r = b) (ht : a + r = t) :
    compose A h (compose A g f ha) ht = compose A (compose A h g hb) f (by omega) := by
  subst a
  subst b
  exact compose_assoc A f g h ht

namespace SimplexData

/-- 概要：最初の切断の右成分をさらに切断して合成した値。
方針：右成分の切断合成を、元の左成分と合成する。
規約：HA Proposition 1.3.1.10。使われ方：三重合成の右からの二重切断。 -/
def nestedCutRight {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j l : Fin (n + 1)) :
    GradedHom A (s.obj a) (s.obj b) (k + 1 + 1) :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 then
    compose A (s.cutCompose (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)) l)
      (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ))) (by omega)
  else 0

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.SimplexData (nestedCutRight)


/-- 概要：最後の切断の左成分をさらに切断して合成した値。
方針：左成分の切断合成を、元の右成分と合成する。
規約：HA Proposition 1.3.1.10。使われ方：三重合成の左からの二重切断。 -/
def nestedCutLeft {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j l : Fin (n + 1)) :
    GradedHom A (s.obj a) (s.obj b) (k + 1 + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 then
    compose A (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ)))
      (s.cutCompose (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ)) j) (by omega)
  else 0

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.SimplexData (nestedCutLeft)


/-- 概要：所属する二点を昇順に切断した三重合成は、二つの切断順で一致する。
方針：中央の集合を共通の区間にそろえ、切断の濃度の等式と合成の結合律を適用する。
規約：HA Proposition 1.3.1.10。使われ方：三重合成項の共通の値への同定。 -/
lemma nestedCutRight_eq_left {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j l : Fin (n + 1)) (hj : j ∈ I) (hl : l ∈ I) (hjl : j < l) :
    s.nestedCutRight I a b k j l = s.nestedCutLeft I a b k j l := by
  have hsumj : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  have hsuml : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hl
    omega
  have hRR : (I.filter (j ≤ ·)).filter (l ≤ ·) = I.filter (l ≤ ·) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hjl.le.trans h.2⟩, h.2⟩⟩
  have hLL : (I.filter (· ≤ l)).filter (· ≤ j) = I.filter (· ≤ j) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hjl.le⟩, h.2⟩⟩
  have hM : (I.filter (· ≤ l)).filter (j ≤ ·) = (I.filter (j ≤ ·)).filter (· ≤ l) := by
    ext x
    simp only [Finset.mem_filter]
    tauto
  have hjL : j ∈ I.filter (· ≤ l) := Finset.mem_filter.mpr ⟨hj, hjl.le⟩
  have hlR : l ∈ I.filter (j ≤ ·) := Finset.mem_filter.mpr ⟨hl, hjl.le⟩
  have hleft : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - (((I.filter (j ≤ ·)).filter (· ≤ l)).card : ℤ)) =
      (2 - ((I.filter (· ≤ l)).card : ℤ)) + 1 := by
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hjL
    rw [hLL, hM] at hc
    omega
  have hright : (2 - (((I.filter (j ≤ ·)).filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) =
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) + 1 := by
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hlR
    rw [hRR] at hc
    omega
  unfold nestedCutRight nestedCutLeft
  rw [dite_eq_left hsumj, dite_eq_left hsuml]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  rw [hRR, hLL, hM, dite_eq_left hright, dite_eq_left hleft]
  exact (compose_assoc_of_sum _ _ _ hleft hright (by omega)).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.SimplexData (nestedCutRight_eq_left)


end SimplexData

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut
