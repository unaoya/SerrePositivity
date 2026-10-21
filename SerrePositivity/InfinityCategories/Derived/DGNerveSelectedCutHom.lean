module
public import SerrePositivity.InfinityCategories.Derived.DGNerveSelectedCutIndex
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms
/-!
概要：選択した第一成分の削除・左右分割を元の実 Hom へ同定する。
方針：同じ添字・次数の異種等号を使い、元の単体の同じ cochain を比較する。
規約：元の実 cochain と同じ有限切断集合を使う。使われ方：tensor 候補の全次元 HA の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveSelectedCutHom_heq {n : ℕ} (s : SimplexData R D n)
    (I S : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hab : a < b) (hc : ∀ j ∈ S, a < j ∧ j < b)
    (hIS : I = insert a (insert b S)) (hdeg : k = -(S.card : ℤ)) :
    HEq (s.hom I a b k hI ha hb hk) (dgNerveSelectedCutHom R D s a b S hab hc) := by
  unfold dgNerveSelectedCutHom
  dsimp only
  exact s.hom_heq_of_indices_degree hIS rfl rfl hdeg
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveSelectedCutHom_erase_heq {n : ℕ} (s : SimplexData R D n)
    (S : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (hab : a < b) (hc : ∀ x ∈ S, a < x ∧ x < b) (hj : j ∈ S)
    (hI : 2 ≤ ((insert a (insert b S)).erase j).card)
    (ha : a = ((insert a (insert b S)).erase j).min' (Index.nonempty hI))
    (hb : b = ((insert a (insert b S)).erase j).max' (Index.nonempty hI))
    (hk : -(S.card : ℤ) + 1 = 2 - (((insert a (insert b S)).erase j).card : ℤ)) :
    HEq (s.hom ((insert a (insert b S)).erase j) a b (-(S.card : ℤ) + 1) hI ha hb hk)
      (dgNerveSelectedCutHom R D s a b (S.erase j) hab
        (fun x hx => hc x (Finset.mem_erase.mp hx).2)) := by
  apply dgNerveSelectedCutHom_heq R D s _ _ a b _ hI ha hb hk hab
    (fun x hx => hc x (Finset.mem_erase.mp hx).2)
  · exact dgNerveSelectedCutIndex_erase S a b j (hc j hj).1 (hc j hj).2
  · have := Finset.card_erase_add_one hj
    omega
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveSelectedCutHom_left_heq {n : ℕ} (s : SimplexData R D n)
    (S : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (hc : ∀ x ∈ S, a < x ∧ x < b) (hj : j ∈ S)
    (hI : 2 ≤ ((insert a (insert b S)).filter (· ≤ j)).card)
    (ha : a = ((insert a (insert b S)).filter (· ≤ j)).min' (Index.nonempty hI))
    (hb : j = ((insert a (insert b S)).filter (· ≤ j)).max' (Index.nonempty hI)) :
    HEq (s.hom ((insert a (insert b S)).filter (· ≤ j)) a j
        (2 - (((insert a (insert b S)).filter (· ≤ j)).card : ℤ)) hI ha hb rfl)
      (dgNerveSelectedCutHom R D s a j (S.filter (· < j)) (hc j hj).1
        (fun x hx => ⟨(hc x (Finset.mem_filter.mp hx).1).1, (Finset.mem_filter.mp hx).2⟩)) := by
  have hidx := dgNerveSelectedCutIndex_left S a b j hj (hc j hj).1 (hc j hj).2
  have hcard := dgNerveSelectedCutIndex_card (S.filter (· < j)) a j (hc j hj).1
    (fun x hx => ⟨(hc x (Finset.mem_filter.mp hx).1).1, (Finset.mem_filter.mp hx).2⟩)
  apply dgNerveSelectedCutHom_heq R D s _ _ a j _ hI ha hb rfl (hc j hj).1
    (fun x hx => ⟨(hc x (Finset.mem_filter.mp hx).1).1, (Finset.mem_filter.mp hx).2⟩) hidx
  rw [hidx, hcard]
  push_cast
  ring
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveSelectedCutHom_right_heq {n : ℕ} (s : SimplexData R D n)
    (S : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (hc : ∀ x ∈ S, a < x ∧ x < b) (hj : j ∈ S)
    (hI : 2 ≤ ((insert a (insert b S)).filter (j ≤ ·)).card)
    (ha : j = ((insert a (insert b S)).filter (j ≤ ·)).min' (Index.nonempty hI))
    (hb : b = ((insert a (insert b S)).filter (j ≤ ·)).max' (Index.nonempty hI)) :
    HEq (s.hom ((insert a (insert b S)).filter (j ≤ ·)) j b
        (2 - (((insert a (insert b S)).filter (j ≤ ·)).card : ℤ)) hI ha hb rfl)
      (dgNerveSelectedCutHom R D s j b (S.filter (j < ·)) (hc j hj).2
        (fun x hx => ⟨(Finset.mem_filter.mp hx).2, (hc x (Finset.mem_filter.mp hx).1).2⟩)) := by
  have hidx := dgNerveSelectedCutIndex_right S a b j hj (hc j hj).1 (hc j hj).2
  have hcard := dgNerveSelectedCutIndex_card (S.filter (j < ·)) j b (hc j hj).2
    (fun x hx => ⟨(Finset.mem_filter.mp hx).2, (hc x (Finset.mem_filter.mp hx).1).2⟩)
  apply dgNerveSelectedCutHom_heq R D s _ _ j b _ hI ha hb rfl (hc j hj).2
    (fun x hx => ⟨(Finset.mem_filter.mp hx).2, (hc x (Finset.mem_filter.mp hx).1).2⟩) hidx
  rw [hidx, hcard]
  push_cast
  ring
end SerrePositivity.InfinityCategories
