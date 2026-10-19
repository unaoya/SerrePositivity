module
public import SerrePositivity.InfinityCategories.Derived.SpanRightCutReplacement
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

/-- 有効な次数の表示によらず、同じ集合の成分は異種等号で一致する。 -/
lemma hom_heq_of_degrees {m : ℕ} (s : SimplexData R D m)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k l : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hl : l = 2 - (I.card : ℤ)) :
    HEq (s.hom I a b k hI ha hb hk) (s.hom I a b l hI ha hb hl) := by
  have hkl : k = l := hk.trans hl.symm
  cases hkl
  rfl

/-- 後続成分の挿入による脚側右辺の変化は、脚との前合成の符号倍。 -/
lemma spanOnePrefixRhs_replace_suffix {n : ℕ} (s : SimplexData R D (n + 3))
    (f : ∀ x y k (hM : 2 ≤ (spanSuffixFaces n).card),
      x = (spanSuffixFaces n).min' (Index.nonempty hM) →
      y = (spanSuffixFaces n).max' (Index.nonempty hM) →
      k = 2 - ((spanSuffixFaces n).card : ℤ) → GradedHom R (s.obj x) (s.obj y) k)
    (a : Fin (n + 4)) (ha : a < spanApex n) :
    (s.replace (spanSuffixFaces n) f).spanOnePrefixRhs a ha - s.spanOnePrefixRhs a ha =
      -(((n : ℤ) + 1).negOnePow • compose R
        (f (spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
          (by rw [card_spanSuffixFaces]; omega)
          (spanSuffixFaces_min n _) (spanSuffixFaces_max n _)
          (by rw [card_spanSuffixFaces]; push_cast; omega) - s.spanSuffixHom)
        (s.edgeHom a (spanApex n) ha) (by omega)) := by
  have hI : 2 ≤ (insert a (spanSuffixFaces n)).card := by
    rw [card_spanSuffix_insert a ha]
    omega
  have hk : -(n : ℤ) - 1 = 2 - ((insert a (spanSuffixFaces n)).card : ℤ) := by
    rw [card_spanSuffix_insert a ha]
    push_cast
    omega
  have hi : spanApex n ∈ insert a (spanSuffixFaces n) :=
    Finset.mem_insert_of_mem ((mem_spanSuffixFaces_iff_le _).mpr le_rfl)
  have H := s.rhs_replace_rightCut (insert a (spanSuffixFaces n)) a (Fin.last (n + 3))
    (-(n : ℤ) - 1) hI (spanSuffix_insert_min a ha _) (spanSuffix_insert_max a _) hk
    (spanApex n) hi ha (spanApex_lt_last n)
  rw [spanSuffix_insert_rightCut a ha] at H
  rw [show (s.replace (spanSuffixFaces n) f).spanOnePrefixRhs a ha -
    s.spanOnePrefixRhs a ha = _ from H f]
  have hE : (insert a (spanSuffixFaces n)).erase (spanApex n) ≠ spanSuffixFaces n := by
    intro h
    exact spanPrefix_notMem_suffix a ha
      (h ▸ Finset.mem_erase.mpr ⟨ne_of_lt ha, Finset.mem_insert_self _ _⟩)
  have hL : {a, spanApex n} ≠ spanSuffixFaces n := by
    intro h
    exact spanPrefix_notMem_suffix a ha (h ▸ (by simp))
  simp only [term, spanSuffix_insert_leftCut a ha, spanSuffix_insert_rightCut a ha,
    replace, dite_eq_right hE, dite_eq_right hL, ↓reduceDIte]
  try simp only [spanSuffix_insert_leftCut a ha, spanSuffix_insert_rightCut a ha,
    Finset.card_pair (ne_of_lt ha), Nat.cast_ofNat, sub_self]
  rw [compose_sub_left]
  dsimp only [edgeHom, spanSuffixHom]
  have hsign := spanSuffix_insert_sign a ha
  dsimp only [Index.sign] at hsign
  rw [hsign]
  simp only [smul_sub]
  abel_nf
  congr 1
  all_goals congr 1
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [spanSuffix_insert_leftCut a ha, spanSuffix_insert_rightCut a ha,
    card_spanSuffixFaces, Finset.card_pair (ne_of_lt ha), Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [spanSuffix_insert_leftCut a ha, spanSuffix_insert_rightCut a ha,
    card_spanSuffixFaces, Finset.card_pair (ne_of_lt ha), Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals try exact s.hom_heq_of_degrees _ _ _ _ _ _ _ _ _ _
  rw [eqRec_proofFamily_apply
    (P₁ := fun M : Finset (Fin (n + 4)) => 2 ≤ M.card)
    (P₂ := fun M h => spanApex n = M.min' (Index.nonempty h))
    (P₃ := fun M h _ => Fin.last (n + 3) = M.max' (Index.nonempty h))
    (P₄ := fun M _ _ _ =>
      2 - (((insert a (spanSuffixFaces n)).filter (spanApex n ≤ ·)).card : ℤ) =
        2 - (M.card : ℤ))
    (p₁ := by rw [card_spanSuffixFaces]; omega)
    (p₂ := spanSuffixFaces_min n _) (p₃ := spanSuffixFaces_max n _)
    (p₄ := by rw [spanSuffix_insert_rightCut a ha])]
  congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | exact s.hom_heq_of_degrees _ _ _ _ _ _ _ _ _ _
    | (rw [spanSuffix_insert_rightCut a ha, card_spanSuffixFaces]; push_cast; omega)

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
