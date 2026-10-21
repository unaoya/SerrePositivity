module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorSignedCutComposition
public import SerrePositivity.InfinityCategories.Derived.DGNerveCutSplit
public import SerrePositivity.InfinityCategories.Derived.DGNerveSelectedCutHom
/-!
概要：選択点で分割した同じ実 tensor を左右の候補切断項の合成へ同定する。
方針：元の実 cochain の添字・次数を照合し、元の HA 符号の係数式を使う。
規約：同じ全次数の tensor 要素を保つ。使われ方：候補の全 HA の内部項の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 同じ実 tensor 項と候補の切断成分の照合。 -/
lemma dgNerveTensorSelectedSplit_eq_cutTermComposite {n : ℕ}
    (s : SimplexData R B n) (t : SimplexData R C n)
    (I S : Finset (Fin (n + 1))) (a b j : Fin (n + 1)) (hj : j ∈ S)
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b)
    (hP : 2 ≤ (I.filter (· ≤ j)).card)
    (haP : IsLeast ((I.filter (· ≤ j)) : Set (Fin (n + 1))) a)
    (hjP : IsGreatest ((I.filter (· ≤ j)) : Set (Fin (n + 1))) j)
    (hQ : 2 ≤ (I.filter (j ≤ ·)).card)
    (hjQ : IsLeast ((I.filter (j ≤ ·)) : Set (Fin (n + 1))) j)
    (hbQ : IsGreatest ((I.filter (j ≤ ·)) : Set (Fin (n + 1))) b)
    (hcL : ∀ x ∈ S.filter (· < j), x ∈ I.filter (· ≤ j) ∧ a < x ∧ x < j)
    (hcR : ∀ x ∈ S.filter (j < ·), x ∈ I.filter (j ≤ ·) ∧ j < x ∧ x < b) :
    (dgNerveTensorCutSign I a b S +
      (((insert a (insert b S)).filter (j < ·)).card : ℤ)).negOnePow •
      dgTensorElement R (n := k + 1)
        (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : DGTensorCategory R B C))
        (compose R (n := -(S.card : ℤ) + 1)
          (dgNerveSelectedCutHom R B s j b (S.filter (j < ·)) (hc j hj).2.2
            (fun x hx => ⟨(Finset.mem_filter.mp hx).2,
              (hc x (Finset.mem_filter.mp hx).1).2.2⟩))
          (dgNerveSelectedCutHom R B s a j (S.filter (· < j)) (hc j hj).2.1
            (fun x hx => ⟨(hc x (Finset.mem_filter.mp hx).1).2.1,
              (Finset.mem_filter.mp hx).2⟩))
          (by have hcard := dgNerveCutCard_selected_split S j hj; omega))
        (dgNerveCutProduct R C t I a b S hI ha hb hc) (by omega) =
    ((I.filter (j < ·)).card : ℤ).negOnePow • compose R (n := k + 1)
      (dgNerveTensorCutTerm R B C s t (I.filter (j ≤ ·)) j b (S.filter (j < ·))
        (2 - ((I.filter (j ≤ ·)).card : ℤ)) rfl hQ hjQ hbQ hcR)
      (dgNerveTensorCutTerm R B C s t (I.filter (· ≤ j)) a j (S.filter (· < j))
        (2 - ((I.filter (· ≤ j)).card : ℤ)) rfl hP haP hjP hcL)
      (by have hcard := Index.split_card (hc j hj).1; omega) := by
  have hST : S ⊆ (I.erase a).erase b := by
    intro x hx
    have hxI := hc x hx
    exact Finset.mem_erase.mpr ⟨ne_of_lt hxI.2.2,
      Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hxI.2.1), hxI.1⟩⟩
  let fL := dgNerveSelectedCutHom R B s a j (S.filter (· < j)) (hc j hj).2.1
    (fun x hx => ⟨(hc x (Finset.mem_filter.mp hx).1).2.1, (Finset.mem_filter.mp hx).2⟩)
  let fR := dgNerveSelectedCutHom R B s j b (S.filter (j < ·)) (hc j hj).2.2
    (fun x hx => ⟨(Finset.mem_filter.mp hx).2, (hc x (Finset.mem_filter.mp hx).1).2.2⟩)
  let gL := dgNerveCutProduct R C t (I.filter (· ≤ j)) a j (S.filter (· < j)) hP haP hjP hcL
  let gR := dgNerveCutProduct R C t (I.filter (j ≤ ·)) j b (S.filter (j < ·)) hQ hjQ hbQ hcR
  have hF : -((S.filter (· < j)).card : ℤ) + -((S.filter (j < ·)).card : ℤ) =
      -(S.card : ℤ) + 1 := by
    have hcard := dgNerveCutCard_selected_split S j hj
    omega
  have hG : (2 - ((I.filter (· ≤ j)).card : ℤ) + ((S.filter (· < j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) + ((S.filter (j < ·)).card : ℤ)) =
      2 - (I.card : ℤ) + (S.card : ℤ) := by
    have hcard := dgNerveCutCard_selected_split S j hj
    have hsplit := Index.split_card (hc j hj).1
    omega
  have hg : dgNerveCutProduct R C t I a b S hI ha hb hc = compose R gR gL hG := by
    have h := dgNerveCutProduct_split R C t I a b S j hI ha hb hc hj
    unfold dgNerveCutSplitProduct at h
    dsimp only at h
    exact h
  rw [hg, dgNerveTensorCutTerm_eq_selected R B C s t (I.filter (j ≤ ·)) j b
    (S.filter (j < ·)) _ rfl hQ hjQ hbQ hcR (hc j hj).2.2,
    dgNerveTensorCutTerm_eq_selected R B C s t (I.filter (· ≤ j)) a j
      (S.filter (· < j)) _ rfl hP haP hjP hcL (hc j hj).2.1]
  exact dgTensorElement_signed_compose_spec R B C
    (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
    (y := ((s.obj j, t.obj j) : DGTensorCategory R B C))
    (z := ((s.obj b, t.obj b) : DGTensorCategory R B C))
    fL gL fR gR (by omega) (by omega) hF hG
    (by have hcard := Index.split_card (hc j hj).1; omega) (by omega) _ _ _ _ _
    (dgNerveTensorCutSign_native_split_exponent I S a b j hST hj hb.1
      (hc j hj).2.1 (hc j hj).2.2)
end SerrePositivity.InfinityCategories
