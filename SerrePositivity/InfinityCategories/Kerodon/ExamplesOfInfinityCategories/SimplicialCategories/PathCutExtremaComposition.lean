module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutExtrema

/-!
概要：零側と一側の切断座標は、同じラベル側での path の合成を無視する。
方針：合成 path の頂点集合を二つの集合の和として比較する。
規約：中間点が零なら後半、一なら前半の交差部分だけを保持する。
使われ方：左右を結ぶ混合 Hom の豊穣合成則。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 零側で前合成しても、交差部分の最後の零頂点は後半のもの。 -/
lemma pathCutLastZero_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hj Q := by
  let R := (compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi R = _
  apply le_antisymm
  · have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · exact (P.le_right _ hm).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero_start t hj Q)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero t hj Q _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi R).1 hm
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero t hi R _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hj Q).1
      (Or.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hj Q).2)

/-- 一側で後合成しても、交差部分の最後の零頂点は前半のもの。 -/
lemma pathCutLastZero_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi P := by
  let R := (compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi R = _
  apply le_antisymm
  · have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero t hi P _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi R).1 hm
    · have h := t.monotone (Q.left_le _ hm)
      rw [hj, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi R).1] at h
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero t hi R _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi P).1
      (Or.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi P).2)

/-- 零側で前合成しても、交差部分の最初の一頂点は後半のもの。 -/
lemma pathCutFirstOne_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hj : t j = 0) (hk : t k = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hk ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hk Q := by
  let R := (compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hk R = _
  apply le_antisymm
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_le t hk R _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hk Q).1
      (Or.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hk Q).2)
  · have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hk R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · have h := t.monotone (P.le_right _ hm)
      rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hk R).1, hj] at h
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_le t hk Q _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hk R).1 hm

/-- 一側で後合成しても、交差部分の最初の一頂点は前半のもの。 -/
lemma pathCutFirstOne_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hj : t j = 1) (hk : t k = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hk ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj P := by
  let R := (compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hk R = _
  apply le_antisymm
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_le t hk R _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hj P).1
      (Or.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hj P).2)
  · have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hk R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_le t hj P _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hk R).1 hm
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_le_end t hj P).trans (Q.left_le _ hm)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
