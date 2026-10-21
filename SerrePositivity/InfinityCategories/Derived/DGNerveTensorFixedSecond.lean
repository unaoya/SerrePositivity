module
public import SerrePositivity.InfinityCategories.Derived.DGNerveConstantCutProduct
/-!
概要：第二入力を固定した実 tensor 写像を、元の第一因子の dg 包含の nerve へ同定する。
方針：定値切断合成の零・単位の判定と同じ実直積写像を使う。
規約：全単体・全面・退化を保持する。使われ方：二変数 Hom と既存 Hom の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve MonoidalCategory
open scoped BigOperators Simplicial
/-- 元の固定終域における実全単体作用の照合。 -/
lemma dgNerveCutInterior_eq_erase {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    I.filter (fun j => a < j ∧ j < b) = (I.erase a).erase b := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hj, haj, hjb⟩
    exact ⟨ne_of_lt hjb, ne_of_gt haj, hj⟩
  · rintro ⟨hjb, hja, hj⟩
    exact ⟨hj, lt_of_le_of_ne (ha.2 hj) (Ne.symm hja), lt_of_le_of_ne (hb.2 hj) hjb⟩
/-- 元の固定終域における実全単体作用の照合。 -/
lemma dgNerveCutInterior_card {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    (I.filter (fun j => a < j ∧ j < b)).card + 2 = I.card := by
  have hab : a < b := by
    have h := I.min'_lt_max'_of_card (by omega)
    simpa only [← ha.unique (I.isLeast_min' (Index.nonempty hI)),
      ← hb.unique (I.isGreatest_max' (Index.nonempty hI))] using h
  rw [dgNerveCutInterior_eq_erase I a b ha hb]
  have hbE : b ∈ I.erase a := Finset.mem_erase.mpr ⟨ne_of_gt hab, hb.1⟩
  have hA := Finset.card_erase_add_one ha.1
  have hB := Finset.card_erase_add_one hbE
  omega
/-- 元の固定終域における実全単体作用の照合。 -/
lemma dgNerveCutInterior_endpoints {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hab : a < b) : insert a (insert b (I.filter (fun j => a < j ∧ j < b))) = I := by
  rw [dgNerveCutInterior_eq_erase I a b ha hb]
  have hbE : b ∈ I.erase a := Finset.mem_erase.mpr ⟨ne_of_gt hab, hb.1⟩
  rw [Finset.insert_erase hbE, Finset.insert_erase ha.1]
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 元の固定終域における実全単体作用の照合。 -/
lemma dgNerveTensorCutTerm_constant_second_proper {n : ℕ} (s : SimplexData R B n) (x : C)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) (hab : a < b)
    (hS : S ≠ I.filter (fun j => a < j ∧ j < b)) :
    dgNerveTensorCutTerm R B C s
      (PinchedHom.constant (X := dgNerve R C) (Simplex.vertex x) n).toSimplexData
      I a b S k hk hI ha hb hc = 0 := by
  have hST : S ⊆ I.filter (fun j => a < j ∧ j < b) :=
    fun j hj => Finset.mem_filter.mpr (hc j hj)
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hST, hS⟩)
  have hcard := dgNerveCutInterior_card I a b hI ha hb
  have hz := dgNerveCutProduct_constant_zero R C x I a b S hI ha hb hc (by omega)
  rw [dgNerveTensorCutTerm_eq_selected R B C s _ I a b S k hk hI ha hb hc hab, hz]
  simp only [dgTensorElement_zero_right, smul_zero]
/-- 元の固定終域における実全単体作用の照合。 -/
lemma dgNerveTensorCutTerm_constant_second_all {n : ℕ} (s : SimplexData R B n) (x : C)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hab : a < b) :
    dgNerveTensorCutTerm R B C s
      (PinchedHom.constant (X := dgNerve R C) (Simplex.vertex x) n).toSimplexData
      I a b (I.filter (fun j => a < j ∧ j < b)) k hk hI ha hb
      (fun _ hj => Finset.mem_filter.mp hj) =
    dgTensorElement R (n := k)
      (x := ((s.obj a, x) : DGTensorCategory R B C))
      (y := ((s.obj b, x) : DGTensorCategory R B C))
      (s.hom I a b k hI (ha.unique (I.isLeast_min' (Index.nonempty hI)))
        (hb.unique (I.isGreatest_max' (Index.nonempty hI))) hk)
      (unitElement R x).val (add_zero k) := by
  let T := I.filter (fun j => a < j ∧ j < b)
  have hcard := dgNerveCutInterior_card I a b hI ha hb
  have hcT : ∀ j ∈ T, j ∈ I ∧ a < j ∧ j < b := fun _ hj => Finset.mem_filter.mp hj
  change T.card + 2 = I.card at hcard
  have hsign : dgNerveTensorCutSign I a b T = 0 := by
    dsimp only [T]
    rw [dgNerveCutInterior_eq_erase I a b ha hb, dgNerveTensorCutSign_all]
  rw [dgNerveTensorCutTerm_eq_selected R B C s _ I a b T k hk hI ha hb hcT hab,
    hsign, Int.negOnePow_zero, one_smul]
  apply eq_of_heq
  refine dgTensorElement_heq R B C (n := k) (n' := k) rfl rfl (by omega) (by omega) rfl
    _ _ _ _ ?_ ?_ _ _
  · exact (dgNerveSelectedCutHom_heq R B s I T a b k hI _ _ hk hab
      (fun j hj => (hcT j hj).2)
      (dgNerveCutInterior_endpoints I a b ha hb hab).symm (by omega)).symm
  · exact dgNerveCutProduct_constant_unit R C x I a b T hI ha hb hcT (by omega)

/-- 元の固定終域における実全単体作用の照合。 -/
lemma dgNerveTensorHomCandidate_constant_second_eq_all {n : ℕ} (s : SimplexData R B n) (x : C)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hab : a < b) :
    dgNerveTensorHomCandidate R B C s
      (PinchedHom.constant (X := dgNerve R C) (Simplex.vertex x) n).toSimplexData
      I a b k hk hI ha hb =
    dgNerveTensorCutTerm R B C s
      (PinchedHom.constant (X := dgNerve R C) (Simplex.vertex x) n).toSimplexData
      I a b (I.filter (fun j => a < j ∧ j < b)) k hk hI ha hb
      (fun _ hj => Finset.mem_filter.mp hj) := by
  let T := I.filter (fun j => a < j ∧ j < b)
  let A : T.powerset := ⟨T, Finset.mem_powerset.mpr (Finset.Subset.refl T)⟩
  let F := fun S : T.powerset => dgNerveTensorCutTerm R B C s
    (PinchedHom.constant (X := dgNerve R C) (Simplex.vertex x) n).toSimplexData
    I a b S.val k hk hI ha hb
    (fun j hj => Finset.mem_filter.mp (Finset.mem_powerset.mp S.property hj))
  change (∑ S, F S) = F A
  refine Finset.sum_eq_single_of_mem A (Finset.mem_univ A) ?_
  intro S _ hS
  change dgNerveTensorCutTerm R B C s _ I a b S.val k hk hI ha hb _ = 0
  apply dgNerveTensorCutTerm_constant_second_proper R B C s x I a b S.val k hk hI ha hb _ hab
  intro he
  exact hS (Subtype.ext he)
/-- 元の固定終域における実全単体作用の照合。 -/
lemma dgNerveTensorSimplex_constant_second {n : ℕ} (s : Simplex R B n) (x : C) :
    dgNerveTensorSimplex R B C s
      (PinchedHom.constant (X := dgNerve R C) (Simplex.vertex x) n) =
      s.map (dgTensorIncludeFirst R B C x) := by
  apply Simplex.ext
  refine SimplexData.ext
    (s := (dgNerveTensorSimplex R B C s
      (PinchedHom.constant (X := dgNerve R C) (Simplex.vertex x) n)).toSimplexData)
    (t := (s.map (dgTensorIncludeFirst R B C x)).toSimplexData) rfl ?_
  apply heq_of_eq
  funext I a b k hI ha hb hk
  have haI : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbI : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hab : a < b := by
    rw [ha, hb]
    exact I.min'_lt_max'_of_card (by omega)
  change dgNerveTensorHomCandidate R B C s.toSimplexData
    (PinchedHom.constant (X := dgNerve R C) (Simplex.vertex x) n).toSimplexData
    I a b k hk hI haI hbI =
    (dgTensorFirstHom R B C x (s.obj a) (s.obj b)).f k (s.hom I a b k hI ha hb hk)
  rw [dgNerveTensorHomCandidate_constant_second_eq_all R B C s.toSimplexData x
    I a b k hk hI haI hbI hab,
    dgNerveTensorCutTerm_constant_second_all R B C s.toSimplexData x I a b k hk hI haI hbI hab,
    dgTensorFirstHom_apply]
open CartesianMonoidalCategory
/-- 元の固定終域における実全単体作用の照合。 -/
lemma dgNerveTensorProductMap_first (E : Type v) [DGCategory R E] (x : E) :
    lift (𝟙 (dgNerve R B)) (SSet.const (Simplex.vertex x)) ≫ dgNerveTensorProductMap R B E =
      dgNerve.map (dgTensorIncludeFirst R B E x) := by
  ext n s
  change dgNerveTensorSimplex R B E s
    (PinchedHom.constant (X := dgNerve R E) (Simplex.vertex x) n.unop.len) =
      s.map (dgTensorIncludeFirst R B E x)
  exact dgNerveTensorSimplex_constant_second R B E s x
end SerrePositivity.InfinityCategories
