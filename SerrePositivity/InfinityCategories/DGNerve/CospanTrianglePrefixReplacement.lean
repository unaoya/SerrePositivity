module
public import SerrePositivity.InfinityCategories.DGNerve.CospanPrefixReplacement
public import SerrePositivity.InfinityCategories.DGNerve.CospanTwoTailCoordinates

/-! # 先頭成分の置換と三角形側右辺の変化

概要：先頭成分の変化は標準三角形成分との合成の負だけ三角形側右辺を変える。
方針：左切断成分の置換を錐頂点で評価し、正一の符号と合成項の負を使う。
規約：HA Proposition 1.3.1.10。使われ方：候補の最後の三角形方程式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：先頭成分の置換による三角形側右辺の変化は三点成分と先頭成分の変化の合成の負。
方針：錐頂点以外の寄与を消し、その正一符号で合成項の負を残す。
規約：HA Proposition 1.3.1.10。使われ方：未知三角形成分を零とした方程式の検証。 -/
lemma cospanTwoTailRhs_replace_prefix {n : ℕ} (s : SimplexData A D (n + 3))
    (f : ∀ a b k (hM : 2 ≤ (cospanPrefixFaces n).card),
      a = (cospanPrefixFaces n).min' (Index.nonempty hM) →
      b = (cospanPrefixFaces n).max' (Index.nonempty hM) →
      k = 2 - ((cospanPrefixFaces n).card : ℤ) → GradedHom A (s.obj a) (s.obj b) k) :
    (s.replace (cospanPrefixFaces n) f).cospanTwoTailRhs - s.cospanTwoTailRhs =
      -compose A (s.tripleHom (cospanApex n) (cospanFirstTail n) (cospanLastTail n)
          (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
        (f 0 (cospanApex n) (-(n : ℤ))
            (by rw [card_cospanPrefixFaces]; omega)
            (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
            (by rw [card_cospanPrefixFaces]; push_cast; omega) - s.cospanPrefixHom) (by omega) := by
  have hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hk : -(n : ℤ) - 2 = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ) := by
    simp only [Finset.card_univ, Fintype.card_fin]
    push_cast
    omega
  have H := s.rhs_replace_leftCut Finset.univ 0 (cospanLastTail n) (-(n : ℤ) - 2)
    hI (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _) hk
    (cospanApex n) (Finset.mem_univ _) (cospanApex_pos n)
    ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
  rw [cospanUniv_leftCut_apex (n := n)] at H
  rw [show (s.replace (cospanPrefixFaces n) f).cospanTwoTailRhs - s.cospanTwoTailRhs = _ from H f]
  have hAD := (cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)
  have hE : (Finset.univ : Finset (Fin (n + 4))).erase (cospanApex n) ≠
      cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix _ hAD
      (heq ▸ Finset.mem_erase.mpr ⟨ne_of_gt hAD, Finset.mem_univ _⟩)
  have hR : {cospanApex n, cospanFirstTail n, cospanLastTail n} ≠ cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix _ hAD (heq ▸ (by simp))
  have hcard : ({cospanApex n, cospanFirstTail n, cospanLastTail n} :
      Finset (Fin (n + 4))).card = 3 := by
    simp [ne_of_lt (cospanApex_lt_firstTail n), ne_of_lt (cospanFirstTail_lt_lastTail n),
      ne_of_lt hAD]
  simp only [term, cospanUniv_leftCut_apex, cospanUniv_rightCut_apex,
    cospanUniv_above_apex, Finset.card_pair (ne_of_lt (cospanFirstTail_lt_lastTail n)),
    Nat.cast_ofNat, show (2 : ℤ).negOnePow = 1 from by decide, one_smul,
    replace, dite_eq_right hE, dite_eq_right hR, ↓reduceDIte]
  rw [compose_sub_right]
  dsimp only [tripleHom, cospanPrefixHom]
  abel_nf
  congr 1
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [cospanUniv_leftCut_apex, cospanUniv_rightCut_apex,
    card_cospanPrefixFaces, hcard, Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [cospanUniv_rightCut_apex, hcard, Nat.cast_ofNat]; omega)
  rw [eqRec_proofFamily_apply
    (P₁ := fun M : Finset (Fin (n + 4)) => 2 ≤ M.card)
    (P₂ := fun M h => (0 : Fin (n + 4)) = M.min' (Index.nonempty h))
    (P₃ := fun M h _ => cospanApex n = M.max' (Index.nonempty h))
    (P₄ := fun M _ _ _ =>
      2 - (((Finset.univ : Finset (Fin (n + 4))).filter (· ≤ cospanApex n)).card : ℤ) =
        2 - (M.card : ℤ))
    (p₁ := by rw [card_cospanPrefixFaces]; omega)
    (p₂ := cospanPrefixFaces_min n _) (p₃ := cospanPrefixFaces_max n _)
    (p₄ := by rw [cospanUniv_leftCut_apex])]
  congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | (simp only [cospanUniv_leftCut_apex, card_cospanPrefixFaces,
        Nat.cast_add, Nat.cast_ofNat]; omega)

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
