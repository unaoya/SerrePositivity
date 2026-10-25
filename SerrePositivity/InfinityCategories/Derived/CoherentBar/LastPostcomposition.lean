module
public import SerrePositivity.InfinityCategories.DGNerve.LastVertexReplacementData
public import SerrePositivity.InfinityCategories.DGNerve.NestedCut
public import SerrePositivity.InfinityCategories.DGNerve.PinchedRhs
/-!
概要：単体データの最後への成分を、次数零の斉次射で後合成する。
方針：既存の lastReplacement と全次数の結合則を使う。
規約：後合成射の閉性は要求しない。HA 右辺の代数的比較と微分式を分離する。
使われ方：D の BianchiData を正規化実 bar の余錐単体へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

def dgCoherentBarPostLastData {n : ℕ} (s : SimplexData R C (n + 1))
    (Y : C) (ρ : GradedHom R (s.obj (Fin.last (n + 1))) Y 0) :
    SimplexData R C (n + 1) :=
  s.lastReplacement Y (fun J a k hJ ha hb hk =>
    compose R ρ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero k))

lemma dgCoherentBarPostLastData_hom_old {n : ℕ} (s : SimplexData R C (n + 1))
    (Y : C) (ρ : GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (J : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hbl : b ≠ Fin.last (n + 1)) :
    HEq ((dgCoherentBarPostLastData s Y ρ).hom J a b k hJ ha hb hk)
      (s.hom J a b k hJ ha hb hk) :=
  SimplexData.lastReplacement_hom_old s Y _ J a b k hJ ha hb hk hbl

lemma dgCoherentBarPostLastData_hom_last {n : ℕ} (s : SimplexData R C (n + 1))
    (Y : C) (ρ : GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((dgCoherentBarPostLastData s Y ρ).hom J a (Fin.last (n + 1)) k hJ ha hb hk)
      (compose R ρ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero k)) :=
  SimplexData.lastReplacement_hom_last s Y _ J a k hJ ha hb hk

lemma dgCoherentBarPostLastData_front {n : ℕ} (s : SimplexData R C (n + 1))
    (Y : C) (ρ : GradedHom R (s.obj (Fin.last (n + 1))) Y 0) :
    (dgCoherentBarPostLastData s Y ρ).pullback Fin.castSuccOrderEmb.toOrderHom =
      s.pullback Fin.castSuccOrderEmb.toOrderHom :=
  SimplexData.lastReplacement_front s Y _


lemma dgCoherentBarHom_units_smul_heq {x y x' y' : C} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l) (c : ℤˣ)
    (f : GradedHom R x y k) (g : GradedHom R x' y' l) (hfg : HEq f g) :
    HEq (c • f) (c • g) := by
  cases hx
  cases hy
  cases hk
  cases eq_of_heq hfg
  rfl

lemma dgCoherentBarPostLastData_term {n : ℕ} (s : SimplexData R C (n + 1))
    (Y : C) (ρ : GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (j : Fin (n + 2)) (hj : j ∈ J) (haj : a < j) (hjl : j < Fin.last (n + 1)) :
    HEq ((dgCoherentBarPostLastData s Y ρ).term J a (Fin.last (n + 1)) k hJ ha hb hk
      j hj haj hjl)
      (compose R ρ (s.term J a (Fin.last (n + 1)) k hJ ha hb hk j hj haj hjl)
        (add_zero (k + 1))) := by
  have hxa := SimplexData.lastReplacementObj_of_ne s Y a
    (ne_of_lt (haj.trans hjl))
  have hxj := SimplexData.lastReplacementObj_of_ne s Y j (ne_of_lt hjl)
  have hxb := SimplexData.lastReplacementObj_last s Y
  unfold SimplexData.term
  rw [DGNerve.compose_units_smul_right, DGNerve.compose_sub_right]
  apply dgCoherentBarHom_units_smul_heq hxa hxb rfl
  apply gradedHom_sub_heq hxa hxb rfl
  · exact dgCoherentBarPostLastData_hom_last s Y ρ _ _ _ _ _ _ _
  · have hamin : IsLeast (J : Set (Fin (n + 2))) a := by
      rw [ha]; exact J.isLeast_min' _
    have hbmax : IsGreatest (J : Set (Fin (n + 2))) (Fin.last (n + 1)) := by
      rw [hb]; exact J.isGreatest_max' _
    let fl := s.hom (J.filter (· ≤ j)) a j (2 - ((J.filter (· ≤ j)).card : ℤ))
      (Index.left_two hamin.1 hj haj) (Index.left_min hamin haj.le _)
      (Index.left_max hj _) rfl
    let fr := s.hom (J.filter (j ≤ ·)) j (Fin.last (n + 1))
      (2 - ((J.filter (j ≤ ·)).card : ℤ))
      (Index.right_two hj hbmax.1 hjl) (Index.right_min hj _)
      (Index.right_max hbmax hjl.le _) rfl
    refine HEq.trans (gradedHom_compose_heq hxa hxj hxb rfl rfl rfl
      (p := 2 - ((J.filter (· ≤ j)).card : ℤ))
      (q := 2 - ((J.filter (j ≤ ·)).card : ℤ))
      (p' := 2 - ((J.filter (· ≤ j)).card : ℤ))
      (q' := 2 - ((J.filter (j ≤ ·)).card : ℤ))
      (k := k + 1) (k' := k + 1)
      _ _ (compose R ρ fr (add_zero _)) fl ?_ ?_ (by have := Index.split_card hj; omega)
        (by have := Index.split_card hj; omega)) (heq_of_eq ?_)
    · exact dgCoherentBarPostLastData_hom_last s Y ρ _ _ _ _ _ _ _
    · exact dgCoherentBarPostLastData_hom_old s Y ρ _ _ _ _ _ _ _ _ (ne_of_lt hjl)
    · exact (DGNerve.compose_assoc_of_sum fl fr ρ
      (by have := Index.split_card hj; omega) (add_zero _) (add_zero _)).symm


lemma dgCoherentBarPostLastData_rhs {n : ℕ} (s : SimplexData R C (n + 1))
    (Y : C) (ρ : GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((dgCoherentBarPostLastData s Y ρ).rhs J a (Fin.last (n + 1)) k hJ ha hb hk)
      (compose R ρ (s.rhs J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero (k + 1))) := by
  have hxa := SimplexData.lastReplacementObj_of_ne s Y a
    (ha ▸ PinchedHom.min_ne_last J hJ)
  have hxb := SimplexData.lastReplacementObj_last s Y
  unfold SimplexData.rhs
  rw [DGNerve.compose_sum_right]
  apply sum_heq_of_obj_eq hxa hxb
  intro j
  split_ifs with h
  · exact dgCoherentBarPostLastData_term s Y ρ J a k hJ ha hb hk j.val j.property h.1 h.2
  · rw [DGNerve.compose_zero]
    exact gradedHom_zero_heq hxa hxb rfl


lemma dgCoherentBarPostLastData_equation_last {n : ℕ} (s : SimplexData R C (n + 1))
    (Y : C) (ρ : GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (θ : GradedHom R (s.obj (Fin.last (n + 1))) (s.obj (Fin.last (n + 1))) 1)
    (hρ : differential R ρ = compose R ρ θ (add_zero 1))
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hclosed : differential R (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) = 0)
    (hrhs : s.rhs J a (Fin.last (n + 1)) k hJ ha hb hk =
      compose R θ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) rfl) :
    differential R ((dgCoherentBarPostLastData s Y ρ).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk) =
    (dgCoherentBarPostLastData s Y ρ).rhs J a (Fin.last (n + 1)) k hJ ha hb hk := by
  have hx := SimplexData.lastReplacementObj_of_ne s Y a
    (ha ▸ PinchedHom.min_ne_last J hJ)
  have hy := SimplexData.lastReplacementObj_last s Y
  have hhom := dgCoherentBarPostLastData_hom_last s Y ρ J a k hJ ha hb hk
  have hd := gradedHom_differential_heq hx hy rfl _ _ hhom
  have he : differential R
      (compose R ρ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero k)) =
      compose R ρ (s.rhs J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero (k + 1)) := by
    rw [differential_compose, hρ, hclosed, DGNerve.compose_zero, smul_zero, add_zero, hrhs]
    exact (DGNerve.compose_assoc_of_sum _ θ ρ rfl (add_zero 1) (add_zero (k + 1))).symm
  exact eq_of_heq (hd.trans ((heq_of_eq he).trans
    (dgCoherentBarPostLastData_rhs s Y ρ J a k hJ ha hb hk).symm))

end SerrePositivity.InfinityCategories
