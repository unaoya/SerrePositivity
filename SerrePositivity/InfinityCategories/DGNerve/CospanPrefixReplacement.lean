module
public import SerrePositivity.InfinityCategories.DGNerve.LeftCutReplacement
public import SerrePositivity.InfinityCategories.DGNerve.ProofFamilyTransport
public import SerrePositivity.InfinityCategories.DGNerve.CospanResidualCoordinates

/-! # 先頭成分の置換と脚側右辺の変化

概要：先頭成分を置き換えると、脚側の右辺は脚と成分の変化の合成だけ変わる。
方針：左切断の置換の一項公式を錐頂点で評価する。
規約：HA Proposition 1.3.1.10。使われ方：候補の脚側の方程式の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：先頭成分の置換による脚側右辺の変化は、脚と先頭成分の変化の合成。
方針：錐頂点以外の寄与を消し、その負一符号と合成項の負を相殺する。
規約：HA Proposition 1.3.1.10。使われ方：未知脚成分を零とした方程式を検証する。 -/
lemma cospanOneTailRhs_replace_prefix {n : ℕ} (s : SimplexData A D (n + 3))
    (f : ∀ a b k (hM : 2 ≤ (cospanPrefixFaces n).card),
      a = (cospanPrefixFaces n).min' (Index.nonempty hM) →
      b = (cospanPrefixFaces n).max' (Index.nonempty hM) →
      k = 2 - ((cospanPrefixFaces n).card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (b : Fin (n + 4)) (hb : cospanApex n < b) :
    (s.replace (cospanPrefixFaces n) f).cospanOneTailRhs b hb - s.cospanOneTailRhs b hb =
      compose A (s.edgeHom (cospanApex n) b hb)
        (f 0 (cospanApex n) (-(n : ℤ))
            (by rw [card_cospanPrefixFaces]; omega)
            (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
            (by rw [card_cospanPrefixFaces]; push_cast; omega) - s.cospanPrefixHom) (by omega) := by
  have hI : 2 ≤ (insert b (cospanPrefixFaces n)).card := by
    rw [card_cospanPrefix_insert b hb]
    omega
  have hk : -(n : ℤ) - 1 = 2 - ((insert b (cospanPrefixFaces n)).card : ℤ) := by
    rw [card_cospanPrefix_insert b hb]
    push_cast
    omega
  have hi : cospanApex n ∈ insert b (cospanPrefixFaces n) :=
    Finset.mem_insert_of_mem ((mem_cospanPrefixFaces_iff_le _).mpr le_rfl)
  have H := s.rhs_replace_leftCut (insert b (cospanPrefixFaces n)) 0 b (-(n : ℤ) - 1)
    hI (cospanPrefix_insert_min _ _) (cospanPrefix_insert_max _ hb _) hk
    (cospanApex n) hi (cospanApex_pos n) hb
  rw [cospanPrefix_insert_leftCut (n := n) b] at H
  rw [show (s.replace (cospanPrefixFaces n) f).cospanOneTailRhs b hb -
      s.cospanOneTailRhs b hb = _ from H f]
  have hE : (insert b (cospanPrefixFaces n)).erase (cospanApex n) ≠ cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix b hb (heq ▸ Finset.mem_erase.mpr
      ⟨ne_of_gt hb, Finset.mem_insert_self _ _⟩)
  have hR : {cospanApex n, b} ≠ cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix b hb (heq ▸ (by simp))
  simp only [term, cospanPrefix_insert_leftCut, cospanPrefix_insert_rightCut b hb,
    cospanPrefix_insert_above b hb, Finset.card_singleton, Nat.cast_one, Int.negOnePow_one,
    Units.neg_smul, one_smul, replace, dite_eq_right hE, dite_eq_right hR, ↓reduceDIte]
  try simp only [cospanPrefix_insert_leftCut, cospanPrefix_insert_rightCut b hb,
    Finset.card_pair (ne_of_lt hb), Nat.cast_ofNat, sub_self]
  rw [compose_sub_right]
  dsimp only [edgeHom, cospanPrefixHom]
  abel_nf
  congr 1
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [cospanPrefix_insert_leftCut, cospanPrefix_insert_rightCut b hb,
    card_cospanPrefixFaces, Finset.card_pair (ne_of_lt hb), Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [cospanPrefix_insert_leftCut, cospanPrefix_insert_rightCut b hb,
    card_cospanPrefixFaces, Finset.card_pair (ne_of_lt hb), Nat.cast_add, Nat.cast_ofNat]; omega)
  rw [eqRec_proofFamily_apply
    (P₁ := fun M : Finset (Fin (n + 4)) => 2 ≤ M.card)
    (P₂ := fun M h => (0 : Fin (n + 4)) = M.min' (Index.nonempty h))
    (P₃ := fun M h _ => cospanApex n = M.max' (Index.nonempty h))
    (P₄ := fun M _ _ _ =>
      2 - (((insert b (cospanPrefixFaces n)).filter (· ≤ cospanApex n)).card : ℤ) =
        2 - (M.card : ℤ))
    (p₁ := by rw [card_cospanPrefixFaces]; omega)
    (p₂ := cospanPrefixFaces_min n _) (p₃ := cospanPrefixFaces_max n _)
    (p₄ := by rw [cospanPrefix_insert_leftCut])]
  congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | (simp only [cospanPrefix_insert_leftCut, card_cospanPrefixFaces,
        Nat.cast_add, Nat.cast_ofNat]; omega)

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
