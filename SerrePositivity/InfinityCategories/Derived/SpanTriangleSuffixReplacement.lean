module
public import SerrePositivity.InfinityCategories.Derived.SpanSuffixReplacement
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixCoordinates
public import SerrePositivity.InfinityCategories.Derived.SpanResidualCoordinates
public import SerrePositivity.InfinityCategories.DGNerve.ProofFamilyTransport

/-! # 後続成分の置換による脚側右辺の変化

概要：後続成分を挿入したときの一点追加集合の右辺の変化を計算する。
方針：余錐頂点における右切断の置換により、一つの合成項だけが変わる。
規約：HA Proposition 1.3.1.10。使われ方：D7 の A・B・C 側の未知方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData
open DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 後続成分の挿入による最上位右辺の変化は、標準三角形成分との合成。 -/
lemma spanTwoPrefixRhs_replace_suffix {n : ℕ} (s : SimplexData R D (n + 3))
    (f : ∀ x y k (hM : 2 ≤ (spanSuffixFaces n).card),
      x = (spanSuffixFaces n).min' (Index.nonempty hM) →
      y = (spanSuffixFaces n).max' (Index.nonempty hM) →
      k = 2 - ((spanSuffixFaces n).card : ℤ) → GradedHom R (s.obj x) (s.obj y) k) :
    (s.replace (spanSuffixFaces n) f).spanTwoPrefixRhs - s.spanTwoPrefixRhs =
      -(((n : ℤ) + 1).negOnePow • compose R
        (f (spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
          (by rw [card_spanSuffixFaces]; omega)
          (spanSuffixFaces_min n _) (spanSuffixFaces_max n _)
          (by rw [card_spanSuffixFaces]; push_cast; omega) - s.spanSuffixHom)
        (s.tripleHom 0 (spanSecondPrefix n) (spanApex n)
          (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n)) (by omega)) := by
  have hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card := by simp
  have hk : -(n : ℤ) - 2 = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ) := by
    simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega
  have H := s.rhs_replace_rightCut Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    hI (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _) hk
    (spanApex n) (Finset.mem_univ _) (spanApex_pos n) (spanApex_lt_last n)
  rw [spanUniv_rightCut_apex] at H
  rw [show (s.replace (spanSuffixFaces n) f).spanTwoPrefixRhs - s.spanTwoPrefixRhs = _ from H f]
  have hE : (Finset.univ : Finset (Fin (n + 4))).erase (spanApex n) ≠ spanSuffixFaces n := by
    intro h
    exact spanPrefix_notMem_suffix 0 (spanApex_pos n)
      (h ▸ Finset.mem_erase.mpr ⟨ne_of_lt (spanApex_pos n), Finset.mem_univ _⟩)
  have hL : ({0, spanSecondPrefix n, spanApex n} : Finset (Fin (n + 4))) ≠
      spanSuffixFaces n := by
    intro h
    exact spanPrefix_notMem_suffix 0 (spanApex_pos n) (h ▸ (by simp))
  have hcard : ({0, spanSecondPrefix n, spanApex n} : Finset (Fin (n + 4))).card = 3 := by
    simp [ne_of_lt (spanSecondPrefix_pos n), ne_of_lt (spanApex_pos n),
      ne_of_lt (spanSecondPrefix_lt_apex n)]
  simp only [term, spanUniv_leftCut_apex, spanUniv_rightCut_apex,
    replace, dite_eq_right hE, dite_eq_right hL, ↓reduceDIte]
  rw [compose_sub_left]
  dsimp only [tripleHom, spanSuffixHom]
  have hsign := spanUniv_sign_apex n
  dsimp only [Index.sign] at hsign
  rw [hsign]
  simp only [smul_sub]
  abel_nf
  congr 1
  all_goals congr 1
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [spanUniv_leftCut_apex, spanUniv_rightCut_apex,
    card_spanSuffixFaces, hcard, Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [spanUniv_leftCut_apex, spanUniv_rightCut_apex,
    card_spanSuffixFaces, hcard, Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals try exact s.hom_heq_of_degrees _ _ _ _ _ _ _ _ _ _
  rw [eqRec_proofFamily_apply
    (P₁ := fun M : Finset (Fin (n + 4)) => 2 ≤ M.card)
    (P₂ := fun M h => spanApex n = M.min' (Index.nonempty h))
    (P₃ := fun M h _ => Fin.last (n + 3) = M.max' (Index.nonempty h))
    (P₄ := fun M _ _ _ =>
      2 - (((Finset.univ : Finset (Fin (n + 4))).filter (spanApex n ≤ ·)).card : ℤ) =
        2 - (M.card : ℤ))
    (p₁ := by rw [card_spanSuffixFaces]; omega)
    (p₂ := spanSuffixFaces_min n _) (p₃ := spanSuffixFaces_max n _)
    (p₄ := by rw [spanUniv_rightCut_apex])]
  congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | exact s.hom_heq_of_degrees _ _ _ _ _ _ _ _ _ _
    | (rw [spanUniv_rightCut_apex, card_spanSuffixFaces]; push_cast; omega)

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
