module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LastVertexReplacementData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRhs
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]

def dgCoherentBarPostLastData {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1))
    (Y : C) (ρ : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj (Fin.last (n + 1))) Y 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1) :=
  s.lastReplacement Y (fun J a k hJ ha hb hk =>
    _root_.SerrePositivity.DifferentialGraded.compose R ρ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero k))

lemma dgCoherentBarPostLastData_hom_old {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1))
    (Y : C) (ρ : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (J : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hbl : b ≠ Fin.last (n + 1)) :
    HEq ((dgCoherentBarPostLastData s Y ρ).hom J a b k hJ ha hb hk)
      (s.hom J a b k hJ ha hb hk) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacement_hom_old s Y _ J a b k hJ ha hb hk hbl

lemma dgCoherentBarPostLastData_hom_last {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1))
    (Y : C) (ρ : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((dgCoherentBarPostLastData s Y ρ).hom J a (Fin.last (n + 1)) k hJ ha hb hk)
      (_root_.SerrePositivity.DifferentialGraded.compose R ρ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero k)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacement_hom_last s Y _ J a k hJ ha hb hk

lemma dgCoherentBarPostLastData_front {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1))
    (Y : C) (ρ : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj (Fin.last (n + 1))) Y 0) :
    (dgCoherentBarPostLastData s Y ρ).pullback Fin.castSuccOrderEmb.toOrderHom =
      s.pullback Fin.castSuccOrderEmb.toOrderHom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacement_front s Y _


lemma dgCoherentBarHom_units_smul_heq {x y x' y' : C} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l) (c : ℤˣ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R x' y' l) (hfg : HEq f g) :
    HEq (c • f) (c • g) := by
  cases hx
  cases hy
  cases hk
  cases eq_of_heq hfg
  rfl

lemma dgCoherentBarPostLastData_term {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1))
    (Y : C) (ρ : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (j : Fin (n + 2)) (hj : j ∈ J) (haj : a < j) (hjl : j < Fin.last (n + 1)) :
    HEq ((dgCoherentBarPostLastData s Y ρ).term J a (Fin.last (n + 1)) k hJ ha hb hk
      j hj haj hjl)
      (_root_.SerrePositivity.DifferentialGraded.compose R ρ (s.term J a (Fin.last (n + 1)) k hJ ha hb hk j hj haj hjl)
        (add_zero (k + 1))) := by
  have hxa := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_of_ne s Y a
    (ne_of_lt (haj.trans hjl))
  have hxj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_of_ne s Y j (ne_of_lt hjl)
  have hxb := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_last s Y
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right]
  apply dgCoherentBarHom_units_smul_heq hxa hxb rfl
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_sub_heq hxa hxb rfl
  · exact dgCoherentBarPostLastData_hom_last s Y ρ _ _ _ _ _ _ _
  · have hamin : IsLeast (J : Set (Fin (n + 2))) a := by
      rw [ha]; exact J.isLeast_min' _
    have hbmax : IsGreatest (J : Set (Fin (n + 2))) (Fin.last (n + 1)) := by
      rw [hb]; exact J.isGreatest_max' _
    let fl := s.hom (J.filter (· ≤ j)) a j (2 - ((J.filter (· ≤ j)).card : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hamin.1 hj haj) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin haj.le _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl
    let fr := s.hom (J.filter (j ≤ ·)) j (Fin.last (n + 1))
      (2 - ((J.filter (j ≤ ·)).card : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjl) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjl.le _) rfl
    refine HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq hxa hxj hxb rfl rfl rfl
      (p := 2 - ((J.filter (· ≤ j)).card : ℤ))
      (q := 2 - ((J.filter (j ≤ ·)).card : ℤ))
      (p' := 2 - ((J.filter (· ≤ j)).card : ℤ))
      (q' := 2 - ((J.filter (j ≤ ·)).card : ℤ))
      (k := k + 1) (k' := k + 1)
      _ _ (compose R ρ fr (add_zero _)) fl ?_ ?_ (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega)
        (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega)) (heq_of_eq ?_)
    · exact dgCoherentBarPostLastData_hom_last s Y ρ _ _ _ _ _ _ _
    · exact dgCoherentBarPostLastData_hom_old s Y ρ _ _ _ _ _ _ _ _ (ne_of_lt hjl)
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum fl fr ρ
      (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega) (add_zero _) (add_zero _)).symm


lemma dgCoherentBarPostLastData_rhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1))
    (Y : C) (ρ : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((dgCoherentBarPostLastData s Y ρ).rhs J a (Fin.last (n + 1)) k hJ ha hb hk)
      (_root_.SerrePositivity.DifferentialGraded.compose R ρ (s.rhs J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero (k + 1))) := by
  have hxa := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_of_ne s Y a
    (ha ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last J hJ)
  have hxb := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_last s Y
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_heq_of_obj_eq hxa hxb
  intro j
  split_ifs with h
  · exact dgCoherentBarPostLastData_term s Y ρ J a k hJ ha hb hk j.val j.property h.1 h.2
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hxa hxb rfl


lemma dgCoherentBarPostLastData_equation_last {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1))
    (Y : C) (ρ : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (θ : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj (Fin.last (n + 1))) (s.obj (Fin.last (n + 1))) 1)
    (hρ : _root_.SerrePositivity.DifferentialGraded.differential R ρ = _root_.SerrePositivity.DifferentialGraded.compose R ρ θ (add_zero 1))
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hclosed : _root_.SerrePositivity.DifferentialGraded.differential R (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) = 0)
    (hrhs : s.rhs J a (Fin.last (n + 1)) k hJ ha hb hk =
      _root_.SerrePositivity.DifferentialGraded.compose R θ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) rfl) :
    _root_.SerrePositivity.DifferentialGraded.differential R ((dgCoherentBarPostLastData s Y ρ).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk) =
    (dgCoherentBarPostLastData s Y ρ).rhs J a (Fin.last (n + 1)) k hJ ha hb hk := by
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_of_ne s Y a
    (ha ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last J hJ)
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_last s Y
  have hhom := dgCoherentBarPostLastData_hom_last s Y ρ J a k hJ ha hb hk
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq hx hy rfl _ _ hhom
  have he : _root_.SerrePositivity.DifferentialGraded.differential R
      (_root_.SerrePositivity.DifferentialGraded.compose R ρ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero k)) =
      _root_.SerrePositivity.DifferentialGraded.compose R ρ (s.rhs J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero (k + 1)) := by
    rw [differential_compose, hρ, hclosed, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero, hrhs]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ θ ρ rfl (add_zero 1) (add_zero (k + 1))).symm
  exact eq_of_heq (hd.trans ((heq_of_eq he).trans
    (dgCoherentBarPostLastData_rhs s Y ρ J a k hJ ha hb hk).symm))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
