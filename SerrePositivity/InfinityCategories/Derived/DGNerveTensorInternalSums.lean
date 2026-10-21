module
public import SerrePositivity.InfinityCategories.Derived.DGNerveCutInsertionReindex
public import SerrePositivity.InfinityCategories.Derived.DGNerveSelectedCutHom
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorNativeCutSigns
public import SerrePositivity.InfinityCategories.Derived.DGNerveCutProductAtDegree
public import SerrePositivity.InfinityCategories.Derived.DGTensorElementHEq
/-!
概要：削除・挿入の実添字同値に沿い、同じ内部 tensor 項の全和の差が零になることを証明する。
方針：元の選択 Hom・切断合成・係数を比較し、全和を添字同値で移す。
規約：元の実複体の同じ次数で相殺する。使われ方：全 tensor 候補の HA の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped BigOperators
variable (R : Type u) [CommRing R]
/-- 同じ実 cochain による内部削除・追加の全和の比較。 -/
lemma dgNerveSelectedCutHom_heq_indices (D : Type v) [DGCategory R D]
    {n : ℕ} (s : SimplexData R D n) (a b : Fin (n + 1)) (S T : Finset (Fin (n + 1)))
    (hab : a < b) (hcS : ∀ x ∈ S, a < x ∧ x < b) (hcT : ∀ x ∈ T, a < x ∧ x < b)
    (he : S = T) : HEq (dgNerveSelectedCutHom R D s a b S hab hcS)
      (dgNerveSelectedCutHom R D s a b T hab hcT) := by
  subst T
  rfl
variable (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 同じ実 cochain による内部削除・追加の全和の比較。 -/
def dgNerveTensorInternalDeletionSummand {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b)
    (p : DGNerveCutDeletionIndex T) :
    GradedHom R (D := DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) :=
  (dgNerveTensorCutSign I a b p.val.1 +
    (((insert a (insert b p.val.1)).filter (p.val.2 < ·)).card : ℤ)).negOnePow •
    dgTensorElement R (n := k + 1)
      (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
      (y := ((s.obj b, t.obj b) : DGTensorCategory R B C))
      (dgNerveSelectedCutHom R B s a b (p.val.1.erase p.val.2) hab
        (fun x hx => (hT x (p.property.1 (Finset.mem_erase.mp hx).2)).2))
      (dgNerveCutProduct R C t I a b p.val.1 hI ha hb
        (fun x hx => hT x (p.property.1 hx))) (by
          have hcard := Finset.card_erase_add_one p.property.2
          omega)
/-- 同じ実 cochain による内部削除・追加の全和の比較。 -/
def dgNerveTensorInternalInsertionSummand {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b)
    (p : DGNerveCutInsertionIndex T) :
    GradedHom R (D := DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) := by
  have hcA : ∀ x ∈ insert p.val.2 p.val.1, x ∈ I ∧ a < x ∧ x < b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hT _ p.property.2.1
    · exact hT x (p.property.1 hx)
  exact (dgNerveTensorCutSign I a b p.val.1 - (p.val.1.card : ℤ) +
    ((I.filter (p.val.2 < ·)).card : ℤ) - ((p.val.1.filter (p.val.2 < ·)).card : ℤ)).negOnePow •
    dgTensorElement R (n := k + 1)
      (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
      (y := ((s.obj b, t.obj b) : DGTensorCategory R B C))
      (dgNerveSelectedCutHom R B s a b p.val.1 hab
        (fun x hx => (hT x (p.property.1 hx)).2))
      (dgNerveCutProductAtDegree R C t I a b (insert p.val.2 p.val.1)
        (2 - (I.card : ℤ) + (p.val.1.card : ℤ) + 1)
        (by rw [Finset.card_insert_of_notMem p.property.2.2]; push_cast; ring)
        hI ha hb hcA) (by omega)
/-- 同じ実 cochain による内部削除・追加の全和の比較。 -/
lemma dgNerveTensorInternalSummand_transport {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b)
    (p : DGNerveCutInsertionIndex T) :
    dgNerveTensorInternalDeletionSummand R B C s t I T a b k hk hI ha hb hT hab
      ((dgNerveCutInsertionEquiv T).symm p) =
    dgNerveTensorInternalInsertionSummand R B C s t I T a b k hk hI ha hb hT hab p := by
  let U := p.val.1
  let j := p.val.2
  have hjU : j ∉ U := p.property.2.2
  have hcU : ∀ x ∈ U, x ∈ I ∧ a < x ∧ x < b := fun x hx => hT x (p.property.1 hx)
  have hjI := hT j p.property.2.1
  have hcA : ∀ x ∈ insert j U, x ∈ I ∧ a < x ∧ x < b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hjI
    · exact hcU x hx
  have hUT : U ⊆ (I.erase a).erase b := by
    intro x hx
    have hxI := hcU x hx
    exact Finset.mem_erase.mpr ⟨ne_of_lt hxI.2.2,
      Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hxI.2.1), hxI.1⟩⟩
  have hjT : j ∈ (I.erase a).erase b := Finset.mem_erase.mpr
    ⟨ne_of_lt hjI.2.2, Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hjI.2.1), hjI.1⟩⟩
  unfold dgNerveTensorInternalDeletionSummand dgNerveTensorInternalInsertionSummand
  dsimp only [dgNerveCutInsertionEquiv, Equiv.symm]
  simp only [Equiv.coe_fn_mk]
  rw [dgNerveTensorCutSign_native_insert_coefficient I U a b j hUT hjT hjU hb.1
    hjI.2.1 hjI.2.2]
  congr 1
  have hdeg : -(((insert j U).erase j).card : ℤ) = -(U.card : ℤ) := by
    rw [Finset.erase_insert hjU]
  have hKG : 2 - (I.card : ℤ) + (U.card : ℤ) + 1 =
      2 - (I.card : ℤ) + ((insert j U).card : ℤ) := by
    rw [Finset.card_insert_of_notMem hjU]
    push_cast
    ring
  apply eq_of_heq
  refine dgTensorElement_heq R B C (n := k + 1) (n' := k + 1) rfl rfl hdeg hKG.symm rfl
    _ _ _ _ ?_ ?_ _ _
  · exact dgNerveSelectedCutHom_heq_indices R B s a b ((insert j U).erase j) U hab
      (fun x hx => (hcA x (Finset.mem_erase.mp hx).2).2)
      (fun x hx => (hcU x hx).2) (Finset.erase_insert hjU)
  · exact (dgNerveCutProductAtDegree_heq R C t I a b (insert j U)
      (2 - (I.card : ℤ) + (U.card : ℤ) + 1) hKG hI ha hb hcA).symm
/-- 同じ実 cochain による内部削除・追加の全和の比較。 -/
lemma dgNerveTensorInternalSums_eq {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b) :
    (∑ p : DGNerveCutDeletionIndex T,
      dgNerveTensorInternalDeletionSummand R B C s t I T a b k hk hI ha hb hT hab p) =
    ∑ p : DGNerveCutInsertionIndex T,
      dgNerveTensorInternalInsertionSummand R B C s t I T a b k hk hI ha hb hT hab p := by
  calc
    _ = ∑ p : DGNerveCutInsertionIndex T,
        dgNerveTensorInternalDeletionSummand R B C s t I T a b k hk hI ha hb hT hab
          ((dgNerveCutInsertionEquiv T).symm p) :=
      (Equiv.sum_comp (dgNerveCutInsertionEquiv T).symm
        (dgNerveTensorInternalDeletionSummand R B C s t I T a b k hk hI ha hb hT hab)).symm
    _ = _ := Finset.sum_congr rfl (fun p _ =>
      dgNerveTensorInternalSummand_transport R B C s t I T a b k hk hI ha hb hT hab p)
/-- 同じ実 cochain による内部削除・追加の全和の比較。 -/
lemma dgNerveTensorInternalSums_cancel {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b) :
    (∑ p : DGNerveCutDeletionIndex T,
      dgNerveTensorInternalDeletionSummand R B C s t I T a b k hk hI ha hb hT hab p) -
    (∑ p : DGNerveCutInsertionIndex T,
      dgNerveTensorInternalInsertionSummand R B C s t I T a b k hk hI ha hb hT hab p) = 0 :=
  sub_eq_zero.mpr (dgNerveTensorInternalSums_eq R B C s t I T a b k hk hI ha hb hT hab)
end SerrePositivity.InfinityCategories
