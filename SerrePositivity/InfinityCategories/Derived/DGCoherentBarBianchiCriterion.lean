module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiTerminalCoefficients
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarShiftedDetection
public import SerrePositivity.InfinityCategories.DGNerve.LastVertexTwistingBianchi

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarCurvature :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X 2 :=
  let A : (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X 2 :=
    (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
        (dgCoherentBarTheta R D F)
  let B : (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X 2 :=
    compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarTheta R D F) (dgCoherentBarTheta R D F) rfl
  A + B

def dgCoherentBarBianchiTheta {n : ℕ} (σ : I _⦋n⦌) :
    GradedHom R ((dgCoherentBarBianchiData R D F σ).obj (Fin.last (n + 1)))
      ((dgCoherentBarBianchiData R D F σ).obj (Fin.last (n + 1))) 1 :=
  (gradedHomTransportWithHEq (A := R) (D := RightModule R D)
    (dgCoherentBarBianchiData_obj_last R D F σ).symm
    (dgCoherentBarBianchiData_obj_last R D F σ).symm rfl (dgCoherentBarTheta R D F)).val

lemma dgCoherentBarBianchiTheta_heq {n : ℕ} (σ : I _⦋n⦌) :
    HEq (dgCoherentBarBianchiTheta R D F σ) (dgCoherentBarTheta R D F) :=
  (gradedHomTransportWithHEq (A := R) (D := RightModule R D) _ _ _ _).property

lemma dgCoherentBarBianchi_curvature_heq {n : ℕ} (σ : I _⦋n⦌) :
    HEq (differential R (dgCoherentBarBianchiTheta R D F σ) +
      compose R (dgCoherentBarBianchiTheta R D F σ) (dgCoherentBarBianchiTheta R D F σ) rfl)
      (dgCoherentBarCurvature R D F) := by
  have hx := dgCoherentBarBianchiData_obj_last R D F σ
  have ht := dgCoherentBarBianchiTheta_heq R D F σ
  unfold dgCoherentBarCurvature
  exact gradedHom_add_heq (A := R) (D := RightModule R D) hx hx rfl _ _ _ _
    (gradedHom_differential_heq (A := R) (D := RightModule R D) hx hx rfl _ _ ht)
    (gradedHom_compose_heq (A := R) (D := RightModule R D) hx hx hx rfl rfl rfl
      _ _ _ _ ht ht rfl rfl)

lemma dgCoherentBarCurvature_eq_zero_of_bianchi_rhs
    (hRhs : ∀ (n : ℕ) (σ : I _⦋n⦌) (J : Finset (Fin (n + 2)))
      (a : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
      (ha : a = J.min' (Index.nonempty hJ))
      (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)),
      (dgCoherentBarBianchiData R D F σ).rhs J a (Fin.last (n + 1)) k hJ ha hb hk =
        compose R (dgCoherentBarBianchiTheta R D F σ)
          ((dgCoherentBarBianchiData R D F σ).hom J a (Fin.last (n + 1)) k hJ ha hb hk) rfl) :
    dgCoherentBarCurvature R D F = 0 := by
  apply dgCoherentBarHom_eq_zero_of_shiftedInclusions R D F
    (dgCoherentBarGraded R D F) 2
  rintro ⟨n, σ⟩
  let s := dgCoherentBarBianchiData R D F σ
  let θ := dgCoherentBarBianchiTheta R D F σ
  have hEnd : ∀ (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
      (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
      (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)),
      s.residual J a (Fin.last (n + 1)) k hJ ha hb hk =
        -compose R θ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) rfl := by
    intro J a k hJ ha hb hk
    rw [SimplexData.residual, dgCoherentBarBianchiData_last_hom_d R D F,
      hRhs, zero_sub]
  let J : Finset (Fin (n + 1)) := Finset.univ
  have hJ : J.Nonempty := Finset.univ_nonempty
  let V := DGNerve.PinchedHom.withLast J
  let a := (J.min' hJ).castSucc
  have hV := DGNerve.PinchedHom.two_withLast hJ
  have ha := DGNerve.PinchedHom.min_withLast hJ (Index.nonempty hV)
  have hb := DGNerve.PinchedHom.max_withLast J (Index.nonempty hV)
  have hk : -(n : ℤ) = 2 - (V.card : ℤ) := by
    dsimp [V, J]
    rw [DGNerve.PinchedHom.card_withLast]; simp; omega
  have hz := SimplexData.curvature_comp_last_twisting s (Fin.last (n + 1)) θ
    (dgCoherentBarBianchiData_old_equation R D F σ) hEnd V a (-(n : ℤ)) hV ha hb hk
    (dgCoherentBarBianchiData_last_hom_d R D F σ V a (-(n : ℤ)) hV ha hb hk)
    (hRhs n σ V a (-(n : ℤ)) hV ha hb hk)
  have hmin : J.min' hJ = 0 :=
    (J.isLeast_min' hJ).unique ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩
  have hx : s.obj a = dgCoherentBarSource R D F ⟨n, σ⟩ := by
    dsimp [s, a]
    rw [hmin, dgCoherentBarBianchiData_obj_castSucc R D F σ]
    exact coherentDiagramSimplex_obj F σ 0
  have hy := dgCoherentBarBianchiData_obj_last R D F σ
  have hh := dgCoherentBarBianchiData_full_coefficient R D F σ hJ
  have hc := gradedHom_compose_heq (A := R) (D := RightModule R D)
    (p := -(n : ℤ)) (q := 2) (k := -(n : ℤ) + 1 + 1)
    (p' := -(n : ℤ)) (q' := 2) (k' := -(n : ℤ) + 2)
    hx hy hy rfl rfl (show -(n : ℤ) + 1 + 1 = -(n : ℤ) + 2 by omega)
    _ _ _ _ (dgCoherentBarBianchi_curvature_heq R D F σ) hh (by omega) rfl
  exact eq_of_heq (hc.symm.trans ((heq_of_eq hz).trans
    (gradedHom_zero_heq (A := R) (D := RightModule R D)
      (k := -(n : ℤ) + 1 + 1) (l := -(n : ℤ) + 2) hx hy (by omega))))

end SerrePositivity.InfinityCategories
