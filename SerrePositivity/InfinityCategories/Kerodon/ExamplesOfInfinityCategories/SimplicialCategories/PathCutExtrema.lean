module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutMaximum

/-!
概要：二値ラベルを横切る path の、零側の最後と一側の最初の座標。
方針：同じ path の二つの有限部分集合から最大元と最小元を取る。
規約：最後の頂点を追加せず、元の単体の両端でラベルを指定する。
使われ方：左右の Hom パラメーターを結ぶ混合 prism の二つの座標。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 同じ単体内の path に属し、指定した二値ラベルを持つ頂点の集合。 -/
def pathCutVertices {n : ℕ} (t : Fin (n + 1) →o Fin 2) (b : Fin 2)
    {i j : Fin (n + 1)}
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun k => t k = b ∧ ULift.up k ∈ P.I)

/-- 零側の始点を持つ path には零ラベルの頂点がある。 -/
lemma pathCutVertices_zero_nonempty {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    (pathCutVertices t 0 P).Nonempty := by
  classical
  exact ⟨i, by simp [pathCutVertices, hi, P.left]⟩

/-- 一側の終点を持つ path には一ラベルの頂点がある。 -/
lemma pathCutVertices_one_nonempty {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    (pathCutVertices t 1 P).Nonempty := by
  classical
  exact ⟨j, by simp [pathCutVertices, hj, P.right]⟩

/-- path の零ラベルの最後の頂点。 -/
def pathCutLastZero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) : Fin (n + 1) :=
  (pathCutVertices t 0 P).max' (pathCutVertices_zero_nonempty t hi P)

/-- path の一ラベルの最初の頂点。 -/
def pathCutFirstOne {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) : Fin (n + 1) :=
  (pathCutVertices t 1 P).min' (pathCutVertices_one_nonempty t hj P)

/-- 選んだ最後の零頂点は、同じ path に属し零ラベルを持つ。 -/
lemma pathCutLastZero_spec {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    t (pathCutLastZero t hi P) = 0 ∧ ULift.up (pathCutLastZero t hi P) ∈ P.I := by
  classical
  exact (Finset.mem_filter.mp (Finset.max'_mem _
    (pathCutVertices_zero_nonempty t hi P))).2

/-- 選んだ最初の一頂点は、同じ path に属し一ラベルを持つ。 -/
lemma pathCutFirstOne_spec {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    t (pathCutFirstOne t hj P) = 1 ∧ ULift.up (pathCutFirstOne t hj P) ∈ P.I := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _
    (pathCutVertices_one_nonempty t hj P))).2

/-- path の任意の零頂点は、選んだ最後の零頂点以下。 -/
lemma le_pathCutLastZero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (k : Fin (n + 1)) (hk : t k = 0) (hP : ULift.up k ∈ P.I) :
    k ≤ pathCutLastZero t hi P := by
  classical
  apply Finset.le_max'
  simp only [pathCutVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hk, hP⟩

/-- 選んだ最初の一頂点は、path の任意の一頂点以下。 -/
lemma pathCutFirstOne_le {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (k : Fin (n + 1)) (hk : t k = 1) (hP : ULift.up k ∈ P.I) :
    pathCutFirstOne t hj P ≤ k := by
  classical
  apply Finset.min'_le
  simp only [pathCutVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hk, hP⟩

/-- path の包含で最後の零頂点は増加する。 -/
lemma pathCutLastZero_mono {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0)
    {P Q : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)} (h : P.I ⊆ Q.I) :
    pathCutLastZero t hi P ≤ pathCutLastZero t hi Q :=
  le_pathCutLastZero t hi Q _ (pathCutLastZero_spec t hi P).1
    (h (pathCutLastZero_spec t hi P).2)

/-- path の包含で最初の一頂点は減少する。 -/
lemma pathCutFirstOne_antitone {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hj : t j = 1)
    {P Q : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)} (h : P.I ⊆ Q.I) :
    pathCutFirstOne t hj Q ≤ pathCutFirstOne t hj P :=
  pathCutFirstOne_le t hj Q _ (pathCutFirstOne_spec t hj P).1
    (h (pathCutFirstOne_spec t hj P).2)

/-- 零側の最後の頂点は、一側の最初の頂点より真に小さい。 -/
lemma pathCutLastZero_lt_firstOne {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    pathCutLastZero t hi P < pathCutFirstOne t hj P := by
  by_contra h
  have e := t.monotone (le_of_not_gt h)
  rw [(pathCutFirstOne_spec t hj P).1, (pathCutLastZero_spec t hi P).1] at e
  exact (by decide : ¬ (1 : Fin 2) ≤ 0) e

/-- 最後の零頂点は始点以上。 -/
lemma le_pathCutLastZero_start {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    i ≤ pathCutLastZero t hi P := le_pathCutLastZero t hi P i hi P.left

/-- 最初の一頂点は終点以下。 -/
lemma pathCutFirstOne_le_end {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    pathCutFirstOne t hj P ≤ j := pathCutFirstOne_le t hj P j hj P.right

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
