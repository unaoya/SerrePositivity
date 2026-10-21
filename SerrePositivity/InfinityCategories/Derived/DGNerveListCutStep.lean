module
public import SerrePositivity.InfinityCategories.Derived.DGNerveListCutProduct
/-!
概要：昇順の切断合成を、先頭の実 Hom と同じ残りの切断合成の一段へ分ける。
方針：端点と指定次数を明示した実合成を取り出し、再帰等式の同じ枝に照合する。
規約：再帰全体を simp に展開しない。使われ方：全次元の微分式と単体的自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 先頭の指定切断点で区切る、同じ実 cochain の一段の合成。 -/
def dgNerveListCutStep {n : ℕ} (s : SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b j : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + ((j :: L).length : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : (j :: L).Pairwise (· < ·))
    (hc : ∀ z ∈ j :: L, z ∈ I ∧ a < z ∧ z < b) :
    GradedHom R (s.obj a) (s.obj b) k := by
  have hj := hc j (by simp)
  have hp := List.pairwise_cons.mp ho
  let P := I.filter (· ≤ j)
  let Q := I.filter (j ≤ ·)
  have hP : 2 ≤ P.card := Index.left_two ha.1 hj.1 hj.2.1
  have hQ : 2 ≤ Q.card := Index.right_two hj.1 hb.1 hj.2.2
  have hjQ : IsLeast (Q : Set (Fin (n + 1))) j :=
    ⟨Finset.mem_filter.mpr ⟨hj.1, le_rfl⟩, fun _ hk => (Finset.mem_filter.mp hk).2⟩
  have hbQ : IsGreatest (Q : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_filter.mpr ⟨hb.1, hj.2.2.le⟩,
      fun _ hk => hb.2 (Finset.mem_filter.mp hk).1⟩
  have ht : ∀ k ∈ L, k ∈ Q ∧ j < k ∧ k < b := by
    intro k hk
    have hkI := hc k (List.mem_cons_of_mem j hk)
    have hjk := hp.1 k hk
    exact ⟨Finset.mem_filter.mpr ⟨hkI.1, hjk.le⟩, hjk, hkI.2.2⟩
  let first := s.hom P a j (2 - (P.card : ℤ)) hP
    (Index.left_min ha hj.2.1.le (Index.nonempty hP))
    (Index.left_max hj.1 (Index.nonempty hP)) rfl
  let rest := dgNerveListCutProduct R D s Q j b L
    (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
  exact compose R rest first (by
    have hs := Index.split_card hj.1
    dsimp only [P, Q]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
    omega)
/-- 昇順列の実切断合成は、同じ先頭成分と残りの実切断合成へ厳密に分かれる。 -/
lemma dgNerveListCutProduct_cons {n : ℕ} (s : SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b j : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + ((j :: L).length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : (j :: L).Pairwise (· < ·))
    (hc : ∀ z ∈ j :: L, z ∈ I ∧ a < z ∧ z < b) :
    dgNerveListCutProduct R D s I a b (j :: L) k hk hI ha hb ho hc =
      dgNerveListCutStep R D s I a b j L k hk ha hb ho hc := by
  rw [dgNerveListCutProduct]
  dsimp only [List.casesOn]
  rfl
end SerrePositivity.InfinityCategories
