module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.CoherentPathMinimum

/-!
概要：時間切断後の path の最小の正頂点を選び、cone の合成と照合する。
方針：時刻一の正頂点を有限集合に集め、最小元と path の包含・合成を比較する。
規約：始点は初点零でもよく、終点の時刻一だけを仮定する。
使われ方：weighted cone の初点から時刻一の頂点への prism の係数。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories


/-- 時刻一を持つ path の正頂点の添字。 -/
noncomputable def pathCutAfterFirst {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 2)} {j : Fin (n + 1)}
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun k => t k = 1 ∧ ULift.up k.succ ∈ P.I)

/-- 時刻一の終点があるので、選ぶ点の集合は非空。 -/
lemma pathCutAfterFirst_nonempty {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    (pathCutAfterFirst t P).Nonempty := by
  classical
  exact ⟨j, by simp [pathCutAfterFirst, hj, P.right]⟩

/-- 時間切断後の最初の正頂点。 -/
noncomputable def pathCutMinimum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) : Fin (n + 1) :=
  (pathCutAfterFirst t P).min' (pathCutAfterFirst_nonempty t hj P)

/-- 最小点は時刻一を持ち、元の path に属する。 -/
lemma pathCutMinimum_spec {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    t (pathCutMinimum t hj P) = 1 ∧ ULift.up (pathCutMinimum t hj P).succ ∈ P.I := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (pathCutAfterFirst t P) (pathCutAfterFirst_nonempty t hj P))).2

/-- 時刻一の任意の正頂点は、選んだ最小点以上。 -/
lemma pathCutMinimum_le {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 2))) (ULift.up j.succ))
    (k : Fin (n + 1)) (hk : t k = 1) (hP : ULift.up k.succ ∈ P.I) :
    pathCutMinimum t hj P ≤ k := by
  classical
  apply Finset.min'_le
  simp only [pathCutAfterFirst, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hk, hP⟩

/-- path の包含に対して、切断後の最小点は反単調。 -/
lemma pathCutMinimum_antitone {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hj : t j = 1)
    {P Q : Path (ULift.up i : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)}
    (h : P.I ⊆ Q.I) : pathCutMinimum t hj Q ≤ pathCutMinimum t hj P :=
  pathCutMinimum_le t hj Q _ (pathCutMinimum_spec t hj P).1
    (h (pathCutMinimum_spec t hj P).2)

/-- 切断後の最小点は終点以下。 -/
lemma pathCutMinimum_le_end {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    pathCutMinimum t hj P ≤ j := pathCutMinimum_le t hj P j hj P.right

/-- 切断後の最小点は、切断を忘れた最初の正頂点以上。 -/
lemma pathFirstMinimum_le_pathCutMinimum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum P ≤ pathCutMinimum t hj P :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum_le P _ (pathCutMinimum_spec t hj P).2

/-- 中間点が時刻零なら、合成の切断後の最小点は後半で選ばれる。 -/
lemma pathCutMinimum_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {a : Fin (n + 2)} {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    (P : Path (ULift.up a : ULift.{u} (Fin (n + 2))) (ULift.up i.succ))
    (Q : Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    pathCutMinimum t hj ((compFunctor ⟨ULift.up a⟩ ⟨ULift.up i.succ⟩
      (⟨ULift.up j.succ⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))).obj (P, Q)) =
      pathCutMinimum t hj Q := by
  let R := (compFunctor ⟨ULift.up a⟩ ⟨ULift.up i.succ⟩
    (⟨ULift.up j.succ⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))).obj (P, Q)
  change pathCutMinimum t hj R = _
  apply le_antisymm
  · exact pathCutMinimum_le t hj R _ (pathCutMinimum_spec t hj Q).1
      (Or.inr (pathCutMinimum_spec t hj Q).2)
  · have hm := (pathCutMinimum_spec t hj R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · have hle := P.le_right _ hm
      change (pathCutMinimum t hj R).succ ≤ i.succ at hle
      have h := t.monotone (Fin.succ_le_succ_iff.mp hle)
      rw [hi, (pathCutMinimum_spec t hj R).1] at h
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)
    · exact pathCutMinimum_le t hj Q _ (pathCutMinimum_spec t hj R).1 hm

/-- 中間点が時刻一なら、合成の切断後の最小点は前半で選ばれる。 -/
lemma pathCutMinimum_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {a : Fin (n + 2)} {i j : Fin (n + 1)} (hi : t i = 1) (hj : t j = 1)
    (P : Path (ULift.up a : ULift.{u} (Fin (n + 2))) (ULift.up i.succ))
    (Q : Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    pathCutMinimum t hj ((compFunctor ⟨ULift.up a⟩ ⟨ULift.up i.succ⟩
      (⟨ULift.up j.succ⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))).obj (P, Q)) =
      pathCutMinimum t hi P := by
  let R := (compFunctor ⟨ULift.up a⟩ ⟨ULift.up i.succ⟩
    (⟨ULift.up j.succ⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))).obj (P, Q)
  change pathCutMinimum t hj R = _
  apply le_antisymm
  · exact pathCutMinimum_le t hj R _ (pathCutMinimum_spec t hi P).1
      (Or.inl (pathCutMinimum_spec t hi P).2)
  · have hm := (pathCutMinimum_spec t hj R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · exact pathCutMinimum_le t hi P _ (pathCutMinimum_spec t hj R).1 hm
    · have hle := Q.left_le _ hm
      change i.succ ≤ (pathCutMinimum t hj R).succ at hle
      exact (pathCutMinimum_le_end t hi P).trans (Fin.succ_le_succ_iff.mp hle)

/-- 全て時刻一なら、切断後の最小点は既存の最初の正頂点そのもの。 -/
lemma pathCutMinimum_eq_firstMinimum {n : ℕ} {j : Fin (n + 1)}
    (t : Fin (n + 1) →o Fin 2) (ht : ∀ k, t k = 1)
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    pathCutMinimum t (ht j) P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum P := by
  apply le_antisymm
  · exact pathCutMinimum_le t (ht j) P _ (ht _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum_mem P)
  · exact pathFirstMinimum_le_pathCutMinimum t (ht j) P

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
