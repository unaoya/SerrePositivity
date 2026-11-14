module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveSelectedCutHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorNativeCutSigns
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutProductAtDegree
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorElementHEq
/-!
概要：内部削除と切断点追加の実 tensor 項、および削除後の候補の実切断項を比較する。
方針：元の実 cochain の添字・次数を照合し、元の HA 符号の係数式を使う。
規約：同じ全次数の tensor 要素を保つ。使われ方：候補の全 HA の内部項の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ実 tensor 項と候補の切断成分の照合。 -/
lemma dgNerveTensorSelectedDeletion_eq_insertion {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I U : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hcU : ∀ x ∈ U, x ∈ I ∧ a < x ∧ x < b) (hab : a < b)
    (hjI : j ∈ I) (haj : a < j) (hjb : j < b) (hjU : j ∉ U)
    (hcA : ∀ x ∈ insert j U, x ∈ I ∧ a < x ∧ x < b)
    (hE : 2 ≤ ((insert a (insert b (insert j U))).erase j).card)
    (haE : a = ((insert a (insert b (insert j U))).erase j).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE))
    (hbE : b = ((insert a (insert b (insert j U))).erase j).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE))
    (hkE : -((insert j U).card : ℤ) + 1 =
      2 - (((insert a (insert b (insert j U))).erase j).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b (insert j U) +
      (((insert a (insert b (insert j U))).filter (j < ·)).card : ℤ)).negOnePow •
      _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (n := k + 1)
        (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (s.hom ((insert a (insert b (insert j U))).erase j) a b
          (-((insert j U).card : ℤ) + 1) hE haE hbE hkE)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R C t I a b (insert j U) hI ha hb hcA) (by omega) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b U - (U.card : ℤ) +
      ((I.filter (j < ·)).card : ℤ) - ((U.filter (j < ·)).card : ℤ)).negOnePow •
      _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (n := k + 1)
        (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom R B s a b U hab (fun x hx => (hcU x hx).2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R C t I a b (insert j U)
          (2 - (I.card : ℤ) + (U.card : ℤ) + 1)
          (by rw [Finset.card_insert_of_notMem hjU]; push_cast; ring)
          hI ha hb hcA) (by omega) := by
  have hUT : U ⊆ (I.erase a).erase b := by
    intro x hx
    have hxI := hcU x hx
    exact Finset.mem_erase.mpr ⟨ne_of_lt hxI.2.2,
      Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hxI.2.1), hxI.1⟩⟩
  have hjT : j ∈ (I.erase a).erase b := Finset.mem_erase.mpr
    ⟨ne_of_lt hjb, Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt haj), hjI⟩⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign_native_insert_coefficient I U a b j hUT hjT hjU hb.1 haj hjb]
  congr 1
  have hcard := Finset.card_insert_of_notMem hjU
  have hdeg : -((insert j U).card : ℤ) + 1 = -(U.card : ℤ) := by omega
  have hIndex : (insert a (insert b (insert j U))).erase j = insert a (insert b U) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutIndex_erase (insert j U) a b j haj hjb, Finset.erase_insert hjU]
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom_heq R B s _ U a b _ hE haE hbE hkE hab
    (fun x hx => (hcU x hx).2) hIndex hdeg
  have hKG : 2 - (I.card : ℤ) + (U.card : ℤ) + 1 =
      2 - (I.card : ℤ) + ((insert j U).card : ℤ) := by
    rw [hcard]
    push_cast
    ring
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_heq R B C (n := k + 1) (n' := k + 1) rfl rfl hdeg hKG.symm rfl
    _ _ _ _ hf ?_ _ _
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree_heq R C t I a b (insert j U)
    (2 - (I.card : ℤ) + (U.card : ℤ) + 1) hKG hI ha hb hcA).symm
/-- 同じ実 tensor 項と候補の切断成分の照合。 -/
lemma dgNerveTensorUnselectedDeletion_eq_cutTerm {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I S : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b) (hab : a < b)
    (hjI : j ∈ I) (haj : a < j) (hjb : j < b) (hjS : j ∉ S)
    (hE : 2 ≤ (I.erase j).card)
    (haE : IsLeast ((I.erase j) : Set (Fin (n + 1))) a)
    (hbE : IsGreatest ((I.erase j) : Set (Fin (n + 1))) b)
    (hcE : ∀ x ∈ S, x ∈ I.erase j ∧ a < x ∧ x < b) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S - (S.card : ℤ) +
      ((I.filter (j < ·)).card : ℤ) - ((S.filter (j < ·)).card : ℤ)).negOnePow •
      _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (n := k + 1)
        (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom R B s a b S hab (fun x hx => (hc x hx).2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R C t (I.erase j) a b S
          (2 - (I.card : ℤ) + (S.card : ℤ) + 1)
          (by have hcard := Finset.card_erase_add_one hjI; omega) hE haE hbE hcE) (by omega) =
    ((I.filter (j < ·)).card : ℤ).negOnePow •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t (I.erase j) a b S (k + 1)
        (by have hcard := Finset.card_erase_add_one hjI; omega) hE haE hbE hcE := by
  have hST : S ⊆ (I.erase a).erase b := by
    intro x hx
    have hxI := hc x hx
    exact Finset.mem_erase.mpr ⟨ne_of_lt hxI.2.2,
      Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hxI.2.1), hxI.1⟩⟩
  have hjT : j ∈ (I.erase a).erase b := Finset.mem_erase.mpr
    ⟨ne_of_lt hjb, Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt haj), hjI⟩⟩
  have hkE : k + 1 = 2 - ((I.erase j).card : ℤ) := by
    have hcard := Finset.card_erase_add_one hjI
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm_eq_selected R B C s t (I.erase j) a b S (k + 1)
    hkE hE haE hbE hcE hab]
  simp only [smul_smul, ← Int.negOnePow_add]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign_native_erase_coefficient I S a b j hST hjT hjS]
  rw [add_comm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.erase j) a b S) ((I.filter (j < ·)).card : ℤ)]
  congr 1
  have hKG : 2 - (I.card : ℤ) + (S.card : ℤ) + 1 =
      2 - ((I.erase j).card : ℤ) + (S.card : ℤ) := by
    have hcard := Finset.card_erase_add_one hjI
    omega
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_heq R B C (n := k + 1) (n' := k + 1) rfl rfl rfl hKG rfl
    _ _ _ _ (HEq.refl _) ?_ _ _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree_heq R C t (I.erase j) a b S
    (2 - (I.card : ℤ) + (S.card : ℤ) + 1) hKG hE haE hbE hcE
end SerrePositivity.InfinityCategories.Project.DerivedCategories
