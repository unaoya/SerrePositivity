module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBianchiTerminalCoefficients
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarShiftedDetection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LastVertexTwistingBianchi

/-!
概要：実 bar の曲率零を、同じ包含係数の HA 右辺と θ 作用の一致へ帰着する。
方針：実 Bianchi データの閉性と先頭方程式を適用し、全シフト包含で曲率を検出する。
規約：右辺の一致はここでは仮定として明示し、その実証を無条件 MC と取り違えない。
使われ方：列ごとの一次の係数比較から bar の MC を結論する最後の一般段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarCurvature :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 2 :=
  let A : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 2 :=
    (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
  let B : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 2 :=
    compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) rfl
  A + B

def dgCoherentBarBianchiTheta {n : ℕ} (σ : I _⦋n⦌) :
    GradedHom R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).obj (Fin.last (n + 1)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).obj (Fin.last (n + 1))) 1 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := R) (D := RightModule R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F σ).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F σ).symm rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)).val

lemma dgCoherentBarBianchiTheta_heq {n : ℕ} (σ : I _⦋n⦌) :
    HEq (dgCoherentBarBianchiTheta R D F σ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := R) (D := RightModule R D) _ _ _ _).property

lemma dgCoherentBarBianchi_curvature_heq {n : ℕ} (σ : I _⦋n⦌) :
    HEq (_root_.SerrePositivity.DifferentialGraded.differential R (dgCoherentBarBianchiTheta R D F σ) +
      _root_.SerrePositivity.DifferentialGraded.compose R (dgCoherentBarBianchiTheta R D F σ) (dgCoherentBarBianchiTheta R D F σ) rfl)
      (dgCoherentBarCurvature R D F) := by
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F σ
  have ht := dgCoherentBarBianchiTheta_heq R D F σ
  unfold dgCoherentBarCurvature
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (A := R) (D := RightModule R D) hx hx rfl _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := R) (D := RightModule R D) hx hx rfl _ _ ht)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D) hx hx hx rfl rfl rfl
      _ _ _ _ ht ht rfl rfl)

lemma dgCoherentBarCurvature_eq_zero_of_bianchi_rhs
    (hRhs : ∀ (n : ℕ) (σ : I _⦋n⦌) (J : Finset (Fin (n + 2)))
      (a : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
      (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
      (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).rhs J a (Fin.last (n + 1)) k hJ ha hb hk =
        _root_.SerrePositivity.DifferentialGraded.compose R (dgCoherentBarBianchiTheta R D F σ)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).hom J a (Fin.last (n + 1)) k hJ ha hb hk) rfl) :
    dgCoherentBarCurvature R D F = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHom_eq_zero_of_shiftedInclusions R D F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) 2
  rintro ⟨n, σ⟩
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ
  let θ := dgCoherentBarBianchiTheta R D F σ
  have hEnd : ∀ (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
      (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
      (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)),
      s.residual J a (Fin.last (n + 1)) k hJ ha hb hk =
        -_root_.SerrePositivity.DifferentialGraded.compose R θ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) rfl := by
    intro J a k hJ ha hb hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.residual, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_last_hom_d R D F,
      hRhs, zero_sub]
  let J : Finset (Fin (n + 1)) := Finset.univ
  have hJ : J.Nonempty := Finset.univ_nonempty
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J
  let a := (J.min' hJ).castSucc
  have hV := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hV)
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hV)
  have hk : -(n : ℤ) = 2 - (V.card : ℤ) := by
    dsimp [V, J]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; simp; omega
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.curvature_comp_last_twisting s (Fin.last (n + 1)) θ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_old_equation R D F σ) hEnd V a (-(n : ℤ)) hV ha hb hk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_last_hom_d R D F σ V a (-(n : ℤ)) hV ha hb hk)
    (hRhs n σ V a (-(n : ℤ)) hV ha hb hk)
  have hmin : J.min' hJ = 0 :=
    (J.isLeast_min' hJ).unique ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩
  have hx : s.obj a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, σ⟩ := by
    dsimp [s, a]
    rw [hmin, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_castSucc R D F σ]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj F σ 0
  have hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F σ
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_full_coefficient R D F σ hJ
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    (p := -(n : ℤ)) (q := 2) (k := -(n : ℤ) + 1 + 1)
    (p' := -(n : ℤ)) (q' := 2) (k' := -(n : ℤ) + 2)
    hx hy hy rfl rfl (show -(n : ℤ) + 1 + 1 = -(n : ℤ) + 2 by omega)
    _ _ _ _ (dgCoherentBarBianchi_curvature_heq R D F σ) hh (by omega) rfl
  exact eq_of_heq (hc.symm.trans ((heq_of_eq hz).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D)
      (k := -(n : ℤ) + 1 + 1) (l := -(n : ℤ) + 2) hx hy (by omega))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
