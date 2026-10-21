module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorSelectedTermDecomposition
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorSelectedSplit
/-!
概要：選択点の第一 tensor 項を内部削除と左右候補の合成の差へ同定する。
方針：元の実 cochain の次数・添字と符号付き合成を照合する。
規約：同じ実 tensor を保つ。使われ方：全切断和の内部項の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 元の実 tensor 項と候補の境界成分の照合。 -/
def dgNerveTensorSelectedCompositeSummand {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (p : DGNerveCutDeletionIndex T) :
    GradedHom R (D := DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) := by
  let S := p.val.1
  let j := p.val.2
  have hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b := fun x hx => hT x (p.property.1 hx)
  have hjI := hc j p.property.2
  let P := I.filter (· ≤ j)
  let Q := I.filter (j ≤ ·)
  have hP : 2 ≤ P.card := Index.left_two ha.1 hjI.1 hjI.2.1
  have hQ : 2 ≤ Q.card := Index.right_two hjI.1 hb.1 hjI.2.2
  have haP : IsLeast (P : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_filter.mpr ⟨ha.1, hjI.2.1.le⟩,
      fun _ hx => ha.2 (Finset.mem_filter.mp hx).1⟩
  have hjP : IsGreatest (P : Set (Fin (n + 1))) j :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hjQ : IsLeast (Q : Set (Fin (n + 1))) j :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hbQ : IsGreatest (Q : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_filter.mpr ⟨hb.1, hjI.2.2.le⟩,
      fun _ hx => hb.2 (Finset.mem_filter.mp hx).1⟩
  have hcL : ∀ x ∈ S.filter (· < j), x ∈ P ∧ a < x ∧ x < j := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hxj := (Finset.mem_filter.mp hx).2
    exact ⟨Finset.mem_filter.mpr ⟨(hc x hxS).1, hxj.le⟩, (hc x hxS).2.1, hxj⟩
  have hcR : ∀ x ∈ S.filter (j < ·), x ∈ Q ∧ j < x ∧ x < b := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hjx := (Finset.mem_filter.mp hx).2
    exact ⟨Finset.mem_filter.mpr ⟨(hc x hxS).1, hjx.le⟩, hjx, (hc x hxS).2.2⟩
  exact ((I.filter (j < ·)).card : ℤ).negOnePow • compose R (n := k + 1)
    (dgNerveTensorCutTerm R B C s t Q j b (S.filter (j < ·))
      (2 - (Q.card : ℤ)) rfl hQ hjQ hbQ hcR)
    (dgNerveTensorCutTerm R B C s t P a j (S.filter (· < j))
      (2 - (P.card : ℤ)) rfl hP haP hjP hcL)
    (by have hcard := Index.split_card hjI.1; dsimp only [P, Q]; omega)
/-- 元の実 tensor 項と候補の境界成分の照合。 -/
def dgNerveTensorSelectedContribution {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b) (p : DGNerveCutDeletionIndex T) :
    GradedHom R (D := DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) :=
    (dgNerveTensorCutSign I a b p.val.1).negOnePow •
      dgTensorElement R (n := k + 1)
        (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : DGTensorCategory R B C))
        (dgNerveSelectedCutTerm R B s a b p.val.1 hab
          (fun x hx => (hT x (p.property.1 hx)).2) p.val.2 p.property.2)
        (dgNerveCutProduct R C t I a b p.val.1 hI ha hb
          (fun x hx => hT x (p.property.1 hx))) (by omega)
/-- 元の実 tensor 項と候補の境界成分の照合。 -/
lemma dgNerveTensorSelectedTerm_eq_internal_sub_composite {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b) (p : DGNerveCutDeletionIndex T) :
    dgNerveTensorSelectedContribution R B C s t I T a b k hk hI ha hb hT hab p =
      dgNerveTensorInternalDeletionSummand R B C s t I T a b k hk hI ha hb hT hab p -
        dgNerveTensorSelectedCompositeSummand R B C s t I T a b k hk ha hb hT p := by
  let S := p.val.1
  let j := p.val.2
  have hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b := fun x hx => hT x (p.property.1 hx)
  have hjI := hc j p.property.2
  let P := I.filter (· ≤ j)
  let Q := I.filter (j ≤ ·)
  have hP : 2 ≤ P.card := Index.left_two ha.1 hjI.1 hjI.2.1
  have hQ : 2 ≤ Q.card := Index.right_two hjI.1 hb.1 hjI.2.2
  have haP : IsLeast (P : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_filter.mpr ⟨ha.1, hjI.2.1.le⟩,
      fun _ hx => ha.2 (Finset.mem_filter.mp hx).1⟩
  have hjP : IsGreatest (P : Set (Fin (n + 1))) j :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hjQ : IsLeast (Q : Set (Fin (n + 1))) j :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hbQ : IsGreatest (Q : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_filter.mpr ⟨hb.1, hjI.2.2.le⟩,
      fun _ hx => hb.2 (Finset.mem_filter.mp hx).1⟩
  have hcL : ∀ x ∈ S.filter (· < j), x ∈ P ∧ a < x ∧ x < j := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hxj := (Finset.mem_filter.mp hx).2
    exact ⟨Finset.mem_filter.mpr ⟨(hc x hxS).1, hxj.le⟩, (hc x hxS).2.1, hxj⟩
  have hcR : ∀ x ∈ S.filter (j < ·), x ∈ Q ∧ j < x ∧ x < b := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hjx := (Finset.mem_filter.mp hx).2
    exact ⟨Finset.mem_filter.mpr ⟨(hc x hxS).1, hjx.le⟩, hjx, (hc x hxS).2.2⟩
  unfold dgNerveTensorSelectedContribution
  rw [dgNerveTensorSelectedTerm_eq_internal_sub_split R B C s t I T a b k hk hI ha hb hT hab p]
  congr 1
  unfold dgNerveTensorSelectedCompositeSummand
  dsimp only
  exact dgNerveTensorSelectedSplit_eq_cutTermComposite R B C s t I S a b j p.property.2
    k hk hI ha hb hc hP haP hjP hQ hjQ hbQ hcL hcR
end SerrePositivity.InfinityCategories
