module

public import SerrePositivity.InfinityCategories.F1.CoherentPathCutExtrema

/-!
概要：零側と一側の切断座標は、同じラベル側での path の合成を無視する。
方針：合成 path の頂点集合を二つの集合の和として比較する。
規約：中間点が零なら後半、一なら前半の交差部分だけを保持する。
使われ方：左右を結ぶ混合 Hom の豊穣合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories

/-- 零側で前合成しても、交差部分の最後の零頂点は後半のもの。 -/
lemma pathCutLastZero_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    pathCutLastZero t hi ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
    pathCutLastZero t hj Q := by
  let R := (compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)
  change pathCutLastZero t hi R = _
  apply le_antisymm
  · have hm := (pathCutLastZero_spec t hi R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · exact (P.le_right _ hm).trans (le_pathCutLastZero_start t hj Q)
    · exact le_pathCutLastZero t hj Q _ (pathCutLastZero_spec t hi R).1 hm
  · exact le_pathCutLastZero t hi R _ (pathCutLastZero_spec t hj Q).1
      (Or.inr (pathCutLastZero_spec t hj Q).2)

/-- 一側で後合成しても、交差部分の最後の零頂点は前半のもの。 -/
lemma pathCutLastZero_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    pathCutLastZero t hi ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
    pathCutLastZero t hi P := by
  let R := (compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)
  change pathCutLastZero t hi R = _
  apply le_antisymm
  · have hm := (pathCutLastZero_spec t hi R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · exact le_pathCutLastZero t hi P _ (pathCutLastZero_spec t hi R).1 hm
    · have h := t.monotone (Q.left_le _ hm)
      rw [hj, (pathCutLastZero_spec t hi R).1] at h
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)
  · exact le_pathCutLastZero t hi R _ (pathCutLastZero_spec t hi P).1
      (Or.inl (pathCutLastZero_spec t hi P).2)

/-- 零側で前合成しても、交差部分の最初の一頂点は後半のもの。 -/
lemma pathCutFirstOne_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hj : t j = 0) (hk : t k = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    pathCutFirstOne t hk ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
    pathCutFirstOne t hk Q := by
  let R := (compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)
  change pathCutFirstOne t hk R = _
  apply le_antisymm
  · exact pathCutFirstOne_le t hk R _ (pathCutFirstOne_spec t hk Q).1
      (Or.inr (pathCutFirstOne_spec t hk Q).2)
  · have hm := (pathCutFirstOne_spec t hk R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · have h := t.monotone (P.le_right _ hm)
      rw [(pathCutFirstOne_spec t hk R).1, hj] at h
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)
    · exact pathCutFirstOne_le t hk Q _ (pathCutFirstOne_spec t hk R).1 hm

/-- 一側で後合成しても、交差部分の最初の一頂点は前半のもの。 -/
lemma pathCutFirstOne_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hj : t j = 1) (hk : t k = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    pathCutFirstOne t hk ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
    pathCutFirstOne t hj P := by
  let R := (compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)
  change pathCutFirstOne t hk R = _
  apply le_antisymm
  · exact pathCutFirstOne_le t hk R _ (pathCutFirstOne_spec t hj P).1
      (Or.inl (pathCutFirstOne_spec t hj P).2)
  · have hm := (pathCutFirstOne_spec t hk R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · exact pathCutFirstOne_le t hj P _ (pathCutFirstOne_spec t hk R).1 hm
    · exact (pathCutFirstOne_le_end t hj P).trans (Q.left_le _ hm)

end SerrePositivity.InfinityCategories
