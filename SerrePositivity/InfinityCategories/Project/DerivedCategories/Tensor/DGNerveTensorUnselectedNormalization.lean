module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorDeletionTerms
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorInternalSums
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorGradedComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutBoundarySum
/-!
概要：未選択点の第二 tensor 項を削除後候補と内部挿入の差へ同定する。
方針：元の実 cochain の次数・添字と符号付き合成を照合する。
規約：同じ実 tensor を保つ。使われ方：全切断和の内部項の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 元の実 tensor 項と候補の境界成分の照合。 -/
def dgNerveTensorUnselectedContribution {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b)
    (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex T) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b p.val.1).negOnePow •
    ((-(p.val.1.card : ℤ)).negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (n := k + 1)
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom R B s a b p.val.1 hab
        (fun x hx => (hT x (p.property.1 hx)).2))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm R C t I a b p.val.1 p.val.2
        (2 - (I.card : ℤ) + (p.val.1.card : ℤ)) rfl ha hb
        (fun x hx => hT x (p.property.1 hx)) (hT _ p.property.2.1).1
        (hT _ p.property.2.1).2.1 (hT _ p.property.2.1).2.2 p.property.2.2) (by omega))
/-- 元の実 tensor 項と候補の境界成分の照合。 -/
def dgNerveTensorErasedCutSummand {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex T) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) := by
  let U := p.val.1
  let j := p.val.2
  have hj := hT j p.property.2.1
  have hE : 2 ≤ (I.erase j).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two ha.1 hb.1 hj.2.1 hj.2.2
  have haE : IsLeast ((I.erase j) : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_erase.mpr ⟨ne_of_lt hj.2.1, ha.1⟩,
      fun _ hx => ha.2 (Finset.mem_erase.mp hx).2⟩
  have hbE : IsGreatest ((I.erase j) : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hj.2.2), hb.1⟩,
      fun _ hx => hb.2 (Finset.mem_erase.mp hx).2⟩
  have hcE : ∀ x ∈ U, x ∈ I.erase j ∧ a < x ∧ x < b := by
    intro x hx
    have hxI := hT x (p.property.1 hx)
    exact ⟨Finset.mem_erase.mpr
      ⟨fun hxj => p.property.2.2 (by simpa only [hxj] using hx), hxI.1⟩, hxI.2⟩
  exact ((I.filter (j < ·)).card : ℤ).negOnePow •
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t (I.erase j) a b U (k + 1)
      (by have hcard := Finset.card_erase_add_one hj.1; omega) hE haE hbE hcE
/-- 元の実 tensor 項と候補の境界成分の照合。 -/
lemma dgNerveTensorUnselectedContribution_eq_erased_sub_internal {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b)
    (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex T) :
    dgNerveTensorUnselectedContribution R B C s t I T a b k hk ha hb hT hab p =
      dgNerveTensorErasedCutSummand R B C s t I T a b k hk ha hb hT p -
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorInternalInsertionSummand R B C s t I T a b k hk hI ha hb hT hab p := by
  let U := p.val.1
  let j := p.val.2
  have hj := hT j p.property.2.1
  have hcU : ∀ x ∈ U, x ∈ I ∧ a < x ∧ x < b := fun x hx => hT x (p.property.1 hx)
  have hE : 2 ≤ (I.erase j).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two ha.1 hb.1 hj.2.1 hj.2.2
  have haE : IsLeast ((I.erase j) : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_erase.mpr ⟨ne_of_lt hj.2.1, ha.1⟩,
      fun _ hx => ha.2 (Finset.mem_erase.mp hx).2⟩
  have hbE : IsGreatest ((I.erase j) : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hj.2.2), hb.1⟩,
      fun _ hx => hb.2 (Finset.mem_erase.mp hx).2⟩
  have hcE : ∀ x ∈ U, x ∈ I.erase j ∧ a < x ∧ x < b := by
    intro x hx
    have hxI := hcU x hx
    exact ⟨Finset.mem_erase.mpr
      ⟨fun hxj => p.property.2.2 (by simpa only [hxj] using hx), hxI.1⟩, hxI.2⟩
  have hs : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b U + (-(U.card : ℤ) +
      (((I.filter (j < ·)).card : ℤ) - ((U.filter (j < ·)).card : ℤ))) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b U - (U.card : ℤ) +
        ((I.filter (j < ·)).card : ℤ) - ((U.filter (j < ·)).card : ℤ) := by ring
  unfold dgNerveTensorUnselectedContribution _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_units_smul_right R B C, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_sub_right R B C]
  simp only [smul_smul, ← Int.negOnePow_add]
  rw [hs, smul_sub]
  refine congrArg₂ (· - ·) ?_ ?_
  · unfold dgNerveTensorErasedCutSummand
    dsimp only
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorUnselectedDeletion_eq_cutTerm R B C s t I U a b j k hk hcU hab
      hj.1 hj.2.1 hj.2.2 p.property.2.2 hE haE hbE hcE
  · rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
