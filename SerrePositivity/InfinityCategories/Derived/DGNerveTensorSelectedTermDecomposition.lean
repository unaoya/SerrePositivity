module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorInternalSums
public import SerrePositivity.InfinityCategories.Derived.DGNerveSelectedCutRhsSum
public import SerrePositivity.InfinityCategories.Derived.DGTensorGradedComposition
public import SerrePositivity.InfinityCategories.Derived.DGNerveSelectedCutHom
public import SerrePositivity.InfinityCategories.Derived.DGNerveCutSplit
/-!
概要：元の第一 HA 合成を選択 Hom の合成へ移し、第一 tensor 項を内部削除と分割の差へ分ける。
方針：同じ添字・次数と実 Hom 成分の異種等号を使い、元の HA 項を展開する。
規約：同じ実 cochain を使う。使われ方：内部和の相殺と残る候補 HA の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 元の第一 HA 成分と左右の実切断成分の比較。 -/
lemma dgNerveSelectedCutComposition_heq {n : ℕ} (s : SimplexData R D n)
    (S : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (hc : ∀ x ∈ S, a < x ∧ x < b) (hj : j ∈ S)
    (hL : 2 ≤ ((insert a (insert b S)).filter (· ≤ j)).card)
    (haL : a = ((insert a (insert b S)).filter (· ≤ j)).min' (Index.nonempty hL))
    (hjL : j = ((insert a (insert b S)).filter (· ≤ j)).max' (Index.nonempty hL))
    (hR : 2 ≤ ((insert a (insert b S)).filter (j ≤ ·)).card)
    (hjR : j = ((insert a (insert b S)).filter (j ≤ ·)).min' (Index.nonempty hR))
    (hbR : b = ((insert a (insert b S)).filter (j ≤ ·)).max' (Index.nonempty hR))
    (hcomp : (2 - (((insert a (insert b S)).filter (· ≤ j)).card : ℤ)) +
      (2 - (((insert a (insert b S)).filter (j ≤ ·)).card : ℤ)) = -(S.card : ℤ) + 1) :
    HEq (compose R (n := -(S.card : ℤ) + 1)
      (s.hom ((insert a (insert b S)).filter (j ≤ ·)) j b _ hR hjR hbR rfl)
      (s.hom ((insert a (insert b S)).filter (· ≤ j)) a j _ hL haL hjL rfl) hcomp)
      (compose R (n := -(S.card : ℤ) + 1)
        (dgNerveSelectedCutHom R D s j b (S.filter (j < ·)) (hc j hj).2
          (fun x hx => ⟨(Finset.mem_filter.mp hx).2, (hc x (Finset.mem_filter.mp hx).1).2⟩))
        (dgNerveSelectedCutHom R D s a j (S.filter (· < j)) (hc j hj).1
          (fun x hx => ⟨(hc x (Finset.mem_filter.mp hx).1).1, (Finset.mem_filter.mp hx).2⟩))
        (by have hcard := dgNerveCutCard_selected_split S j hj; omega)) := by
  have hidxL := dgNerveSelectedCutIndex_left S a b j hj (hc j hj).1 (hc j hj).2
  have hidxR := dgNerveSelectedCutIndex_right S a b j hj (hc j hj).1 (hc j hj).2
  have hcardL := dgNerveSelectedCutIndex_card (S.filter (· < j)) a j (hc j hj).1
    (fun x hx => ⟨(hc x (Finset.mem_filter.mp hx).1).1, (Finset.mem_filter.mp hx).2⟩)
  have hcardR := dgNerveSelectedCutIndex_card (S.filter (j < ·)) j b (hc j hj).2
    (fun x hx => ⟨(Finset.mem_filter.mp hx).2, (hc x (Finset.mem_filter.mp hx).1).2⟩)
  have hdegL : 2 - (((insert a (insert b S)).filter (· ≤ j)).card : ℤ) =
      -((S.filter (· < j)).card : ℤ) := by
    rw [hidxL, hcardL]
    push_cast
    ring
  have hdegR : 2 - (((insert a (insert b S)).filter (j ≤ ·)).card : ℤ) =
      -((S.filter (j < ·)).card : ℤ) := by
    rw [hidxR, hcardR]
    push_cast
    ring
  refine gradedHom_compose_heq (A := R) rfl rfl rfl hdegL hdegR rfl _ _ _ _ ?_ ?_ _ _
  · exact dgNerveSelectedCutHom_right_heq R D s S a b j hc hj hR hjR hbR
  · exact dgNerveSelectedCutHom_left_heq R D s S a b j hc hj hL haL hjL
variable (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 元の第一 HA 成分と左右の実切断成分の比較。 -/
lemma dgNerveTensorSelectedTerm_eq_internal_sub_split {n : ℕ}
    (s : SimplexData R B n) (t : SimplexData R C n)
    (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b)
    (p : DGNerveCutDeletionIndex T) :
    (dgNerveTensorCutSign I a b p.val.1).negOnePow •
      dgTensorElement R (n := k + 1)
        (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : DGTensorCategory R B C))
        (dgNerveSelectedCutTerm R B s a b p.val.1 hab
          (fun x hx => (hT x (p.property.1 hx)).2) p.val.2 p.property.2)
        (dgNerveCutProduct R C t I a b p.val.1 hI ha hb
          (fun x hx => hT x (p.property.1 hx))) (by omega) =
    dgNerveTensorInternalDeletionSummand R B C s t I T a b k hk hI ha hb hT hab p -
      (dgNerveTensorCutSign I a b p.val.1 +
        (((insert a (insert b p.val.1)).filter (p.val.2 < ·)).card : ℤ)).negOnePow •
        dgTensorElement R (n := k + 1)
          (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
          (y := ((s.obj b, t.obj b) : DGTensorCategory R B C))
          (compose R (n := -(p.val.1.card : ℤ) + 1)
            (dgNerveSelectedCutHom R B s p.val.2 b (p.val.1.filter (p.val.2 < ·))
              (hT p.val.2 (p.property.1 p.property.2)).2.2
              (fun x hx => ⟨(Finset.mem_filter.mp hx).2,
                (hT x (p.property.1 (Finset.mem_filter.mp hx).1)).2.2⟩))
            (dgNerveSelectedCutHom R B s a p.val.2 (p.val.1.filter (· < p.val.2))
              (hT p.val.2 (p.property.1 p.property.2)).2.1
              (fun x hx => ⟨(hT x (p.property.1 (Finset.mem_filter.mp hx).1)).2.1,
                (Finset.mem_filter.mp hx).2⟩))
            (by have hcard := dgNerveCutCard_selected_split p.val.1 p.val.2 p.property.2; omega))
          (dgNerveCutProduct R C t I a b p.val.1 hI ha hb
            (fun x hx => hT x (p.property.1 hx))) (by omega) := by
  let S := p.val.1
  let j := p.val.2
  have hj : j ∈ S := p.property.2
  have hcS : ∀ x ∈ S, a < x ∧ x < b := fun x hx => (hT x (p.property.1 hx)).2
  unfold dgNerveSelectedCutTerm
  dsimp only
  unfold SimplexData.term
  dsimp only
  rw [dgTensorElement_units_smul_left R B C, dgTensorElement_sub_left R B C,
    smul_smul, ← Int.negOnePow_add, smul_sub]
  refine congrArg₂ (· - ·) ?_ ?_
  · unfold dgNerveTensorInternalDeletionSummand
    congr 1
    have hcard := Finset.card_erase_add_one p.property.2
    apply eq_of_heq
    refine dgTensorElement_heq R B C (n := k + 1) (n' := k + 1) rfl rfl
      (by omega) rfl rfl _ _ _ _ ?_ (HEq.refl _) _ _
    exact dgNerveSelectedCutHom_erase_heq R B s S a b j hab hcS hj _ _ _ _
  · congr 1
    apply eq_of_heq
    refine dgTensorElement_heq R B C (n := k + 1) (n' := k + 1) rfl rfl rfl rfl rfl
      _ _ _ _ ?_ (HEq.refl _) _ _
    exact dgNerveSelectedCutComposition_heq R B s S a b j hcS hj _ _ _ _ _ _ _
end SerrePositivity.InfinityCategories
