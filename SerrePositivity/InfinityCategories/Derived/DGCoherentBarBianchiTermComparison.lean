module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiFullComponents
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarFaceInclusionComparison
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarPrefixInclusionComparison

/-!
概要：HA 全体右辺の各内部頂点の寄与を、元の面列と prefix 列の一次和へ同定する。
方針：実削除・左右切断の係数比較に、shift の包含対の消去と元の符号の相殺を適用する。
規約：元の全高次係数・単体ラベル・端点を保持する。
使われ方：bar の θ 作用との全体右辺比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial

private lemma compose_degree_heq {A : Type u} [CommRing A] {C : Type v} [DGCategory A C]
    {x y z : C} {p q k l : ℤ} (g : GradedHom A y z q) (f : GradedHom A x y p)
    (h : p + q = k) (h' : p + q = l) : HEq (compose A g f h) (compose A g f h') := by
  have he : k = l := h.symm.trans h'
  cases he
  rfl

private lemma scalar_heq {A : Type u} [CommRing A] {C : Type v} [DGCategory A C]
    {x y x' y' : C} {k l : ℤ} (hx : x = x') (hy : y = y') (hk : k = l)
    (c : ℤˣ) (f : GradedHom A x y k) (g : GradedHom A x' y' l) (h : HEq f g) :
    HEq (c • f) (c • g) := by
  cases hx
  cases hy
  cases hk
  cases eq_of_heq h
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarBianchiFullTerm_heq_boundaryTerm {n : ℕ} (σ : I _⦋n + 1⦌)
    (i : Fin (n + 1)) :
    HEq (dgCoherentBarBianchiFullTerm R D F σ i)
      (dgCoherentBarUnshiftedBoundaryTerm R D F σ i) := by
  let s := dgCoherentBarBianchiData R D F σ
  let V : Finset (Fin (n + 3)) := Finset.univ
  let j := i.succ.castSucc
  let k : ℤ := -((n + 1 : ℕ) : ℤ)
  let d : ℤ := k + 1
  let M := dgCoherentBarSource R D F ⟨n + 1, σ⟩
  let N := dgCoherentBarSource R D F (dgCoherentBarTail σ (i.val + 1) (by omega))
  let B := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)
  let t : ℕ := n + 1 - (i.val + 1)
  have hi : i.val < n + 1 := i.isLt
  have hd : d = -(n : ℤ) := by dsimp [d, k]; omega
  have ht : (t : ℤ) = (n : ℤ) - (i.val : ℤ) := by dsimp [t]; omega
  have hV := coherentDiagramTop_card (n + 1)
  have ha := coherentDiagramTop_min (n + 1)
  have hb := coherentDiagramTop_max (n + 1)
  have hk : k = 2 - (V.card : ℤ) := by dsimp [k, V]; simp; omega
  have hj : j ∈ V := Finset.mem_univ _
  have haj : (0 : Fin (n + 3)) < j := Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos i)
  have hjb : j < Fin.last (n + 2) := Fin.castSucc_lt_last _
  have hx : s.obj 0 = M := (dgCoherentBarBianchiData_obj_castSucc R D F σ 0).trans
    (coherentDiagramSimplex_obj F σ 0)
  have hy : s.obj j = N := (dgCoherentBarBianchiData_obj_castSucc R D F σ i.succ).trans
    ((coherentDiagramSimplex_obj F σ i.succ).trans
      (dgCoherentBarSource_tail R D F σ (i.val + 1) (by omega)).symm)
  have hz : s.obj (Fin.last (n + 2)) = B := dgCoherentBarBianchiData_obj_last R D F σ
  let A : GradedHom R M B d := compose R (x := M)
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩)) (z := B)
    (dgCoherentBarFaceColumn R D F σ i) (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) M) rfl
  let P : GradedHom R M B d := compose R (x := M)
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩)) (z := B)
    (dgCoherentBarPrefixColumn R D F σ i.val (by omega))
    (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) M) rfl
  have hfe : HEq (s.erasedComponent V 0 (Fin.last (n + 2)) k hV ha hb hk j hj haj hjb)
      (dgCoherentBarShiftedInclusion R D F (dgCoherentBarFace σ i.succ)) := by
    unfold SimplexData.erasedComponent
    exact dgCoherentBarBianchiData_full_deleted R D F σ i _ _ _ _ _
  have hA : HEq A ((n : ℤ).negOnePow •
      dgCoherentBarShiftedInclusion R D F (dgCoherentBarFace σ i.succ)) :=
    (compose_degree_heq (A := R) (C := RightModule R D)
      (x := M) (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
      (z := B) (dgCoherentBarFaceColumn R D F σ i)
      (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) M) rfl (by omega)).trans
        (dgCoherentBarFaceColumn_comp_shiftIn_heq R D F σ i)
  have hAn := scalar_heq (A := R) (C := RightModule R D)
    (dgCoherentBarSource_face_succ R D F σ i).symm rfl hd (n : ℤ).negOnePow _ _ hA
  have hAnn : HEq ((n : ℤ).negOnePow • A)
      (dgCoherentBarShiftedInclusion R D F (dgCoherentBarFace σ i.succ)) := by
    simpa only [smul_smul, Int.units_mul_self, one_smul] using hAn
  have hfe' := hfe.trans hAnn.symm
  have hfl : HEq (s.cutLeft V 0 hV ha j hj haj)
      (dgCoherentBarPrefixHom R D F σ i.val (by omega)) := by
    unfold SimplexData.cutLeft
    exact dgCoherentBarBianchiData_full_left R D F σ i _ _ _ _ _
  have hfr : HEq (s.cutRight V (Fin.last (n + 2)) hV hb j hj hjb)
      (dgCoherentBarShiftedInclusion R D F (dgCoherentBarTail σ (i.val + 1) (by omega))) := by
    unfold SimplexData.cutRight
    exact dgCoherentBarBianchiData_full_right R D F σ i _ _ _ _ _
  have hp : 2 - ((V.filter (· ≤ j)).card : ℤ) = -(i.val : ℤ) := by
    dsimp [V, j]
    rw [dgCoherentBarPrefix_card]
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    omega
  have hq : 2 - ((V.filter (j ≤ ·)).card : ℤ) = -(t : ℤ) := by
    dsimp [V, j]
    rw [dgCoherentBarTail_card]
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  have hsum : -(i.val : ℤ) + -(t : ℤ) = d := by dsimp [d, k]; omega
  let Q : GradedHom R M B d := compose R (x := M) (y := N) (z := B)
    (dgCoherentBarShiftedInclusion R D F (dgCoherentBarTail σ (i.val + 1) (by omega)))
    (dgCoherentBarPrefixHom R D F σ i.val (by omega)) hsum
  have hcomp : HEq (s.cutComposite V 0 (Fin.last (n + 2)) k hV ha hb hk j hj haj hjb) Q := by
    unfold SimplexData.cutComposite
    exact gradedHom_compose_heq (A := R) (D := RightModule R D) hx hy hz hp hq rfl
      _ _ _ _ hfr hfl (by have := Index.split_card hj; omega) hsum
  have hPn := (compose_degree_heq (A := R) (C := RightModule R D)
    (x := M) (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
    (z := B) (dgCoherentBarPrefixColumn R D F σ i.val (by omega))
    (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) M) rfl
    (show -((n + 1 : ℕ) : ℤ) + 1 = 1 - ((n + 1 : ℕ) : ℤ) by omega)).trans
      (heq_of_eq (dgCoherentBarPrefixColumn_comp_shiftIn R D F σ i.val (by omega)))
  have hPr := compose_degree_heq (A := R) (C := RightModule R D) (x := M) (y := N) (z := B)
    ((t : ℤ).negOnePow • dgCoherentBarShiftedInclusion R D F (dgCoherentBarTail σ (i.val + 1) (by omega)))
    (dgCoherentBarPrefixHom R D F σ i.val (by omega))
    (show -(i.val : ℤ) + -(t : ℤ) = 1 - ((n + 1 : ℕ) : ℤ) by omega) hsum
  have hP : P = (t : ℤ).negOnePow • Q :=
    (eq_of_heq (hPn.trans hPr)).trans
      (compose_units_smul_left (A := R) (D := RightModule R D) (t : ℤ).negOnePow _ _ hsum)
  have hQ : Q = (t : ℤ).negOnePow • P := by
    have hh := congrArg (fun z => (t : ℤ).negOnePow • z) hP
    simpa only [smul_smul, Int.units_mul_self, one_smul] using hh.symm
  have hcomp' := hcomp.trans (heq_of_eq hQ)
  have hsub := gradedHom_sub_heq (A := R) (D := RightModule R D) hx hz rfl _ _ _ _ hfe' hcomp'
  let c := Index.sign V j
  have hc : c = ((n : ℤ) + 1 - (i.val : ℤ)).negOnePow := dgCoherentBarBianchiFullTerm_sign n i
  have hcf : c * (n : ℤ).negOnePow = ((i.val : ℤ) + 1).negOnePow := by
    rw [hc, ← Int.negOnePow_add]
    have he : (n : ℤ) + 1 - (i.val : ℤ) + n = 2 * ((n : ℤ) - i.val) + (i.val + 1) := by ring
    rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]
  have hcp : c * (t : ℤ).negOnePow = -(1 : ℤˣ) := by
    rw [hc, ht, ← Int.negOnePow_add]
    have he : (n : ℤ) + 1 - (i.val : ℤ) + (n - i.val) = 2 * ((n : ℤ) - i.val) + 1 := by ring
    rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, Int.negOnePow_one, one_mul]
  have hsc := scalar_heq (A := R) (C := RightModule R D) hx hz rfl c _ _ hsub
  have hlast : c • ((n : ℤ).negOnePow • A - (t : ℤ).negOnePow • P) =
      ((i.val : ℤ) + 1).negOnePow • A + P := by
    rw [smul_sub, smul_smul, smul_smul, hcf, hcp]
    simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul, sub_neg_eq_add]
  change HEq (s.term V 0 (Fin.last (n + 2)) k hV ha hb hk j hj haj hjb)
    (((i.val : ℤ) + 1).negOnePow • A + P)
  rw [SimplexData.term_eq_sub_cutComposite]
  exact hsc.trans (heq_of_eq hlast)

end SerrePositivity.InfinityCategories
