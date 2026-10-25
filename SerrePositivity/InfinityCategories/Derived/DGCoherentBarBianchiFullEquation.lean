module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiFullRhs
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiCriterion

/-!
概要：各元の単体について、末端への全体 HA 右辺を同じ θ の作用と等号で同定する。
方針：正次元は元の有限和比較、零次元は内部点が無いことと頂点列の零を使う。
規約：MC を仮定せず、bar の元の全体成分を保持する。
使われ方：任意の部分集合への制限による無条件 MC の接続。
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

lemma dgCoherentBarBianchiData_hom_univ_heq {n : ℕ} (σ : I _⦋n⦌) :
    HEq ((dgCoherentBarBianchiData R D F σ).hom Finset.univ 0 (Fin.last (n + 1))
      (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
      (coherentDiagramTop_max n) (by simp; omega))
      (dgCoherentBarShiftedInclusion R D F ⟨n, σ⟩) := by
  have hJ : (Finset.univ : Finset (Fin (n + 1))).Nonempty := Finset.univ_nonempty
  have hm : Finset.univ.min' hJ = (0 : Fin (n + 1)) :=
    (Finset.univ.isLeast_min' hJ).unique ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩
  refine HEq.trans ?_ (dgCoherentBarBianchiData_full_coefficient R D F σ hJ)
  exact SimplexData.hom_heq_of_indices_degree _ (dgCoherentBar_withLast_univ n).symm
    (by rw [hm]; rfl) rfl rfl

lemma dgCoherentBarBianchiData_full_equation {n : ℕ} (σ : I _⦋n⦌) :
    (dgCoherentBarBianchiData R D F σ).rhs Finset.univ 0 (Fin.last (n + 1))
      (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
      (coherentDiagramTop_max n) (by simp; omega) =
      compose R (dgCoherentBarBianchiTheta R D F σ)
        ((dgCoherentBarBianchiData R D F σ).hom Finset.univ 0 (Fin.last (n + 1))
          (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
          (coherentDiagramTop_max n) (by simp; omega)) rfl := by
  have hx : (dgCoherentBarBianchiData R D F σ).obj 0 =
      dgCoherentBarSource R D F ⟨n, σ⟩ :=
    (dgCoherentBarBianchiData_obj_castSucc R D F σ 0).trans
      (coherentDiagramSimplex_obj F σ 0)
  have hy := dgCoherentBarBianchiData_obj_last R D F σ
  have hright := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hy hy rfl rfl rfl _ _ _ _ (dgCoherentBarBianchiTheta_heq R D F σ)
    (dgCoherentBarBianchiData_hom_univ_heq R D F σ) rfl rfl
  apply eq_of_heq
  apply HEq.trans _ hright.symm
  cases n with
  | zero =>
    have hl : (dgCoherentBarBianchiData R D F σ).rhs Finset.univ 0 (Fin.last 1)
        (-(0 : ℤ)) (coherentDiagramTop_card 0) (coherentDiagramTop_min 0)
        (coherentDiagramTop_max 0) (by simp) = 0 := by
      unfold SimplexData.rhs
      apply Finset.sum_eq_zero
      intro j _
      split_ifs with h
      · have h0 : 0 < j.val.val := h.1
        have h1 : j.val.val < 1 := h.2
        omega
      · rfl
    have ht : compose R (x := dgCoherentBarSource R D F ⟨0, σ⟩)
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarShiftedInclusion R D F ⟨0, σ⟩) rfl = 0 := by
      rw [dgCoherentBarTheta_comp_shiftedInclusion R D F]
      change (0 : ℤ).negOnePow • compose R
        (x := dgCoherentBarSource R D F ⟨0, σ⟩)
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨0, σ⟩))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        0 (moduleShiftInElement R D 0 (dgCoherentBarSource R D F ⟨0, σ⟩)) rfl = 0
      rw [zero_compose, smul_zero]
    exact (heq_of_eq hl).trans ((gradedHom_zero_heq (A := R) (D := RightModule R D)
      hx hy rfl).trans (heq_of_eq ht.symm))
  | succ n => exact dgCoherentBarBianchiData_full_rhs_heq_theta R D F σ


lemma dgCoherentBarBianchiData_full_rhs_heq_theta_all {n : ℕ} (σ : I _⦋n⦌) :
    HEq ((dgCoherentBarBianchiData R D F σ).rhs Finset.univ 0 (Fin.last (n + 1))
      (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
      (coherentDiagramTop_max n) (by simp; omega))
      (compose R (x := dgCoherentBarSource R D F ⟨n, σ⟩)
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarShiftedInclusion R D F ⟨n, σ⟩) rfl) := by
  have hx : (dgCoherentBarBianchiData R D F σ).obj 0 = dgCoherentBarSource R D F ⟨n, σ⟩ :=
    (dgCoherentBarBianchiData_obj_castSucc R D F σ 0).trans
      (coherentDiagramSimplex_obj F σ 0)
  have hy := dgCoherentBarBianchiData_obj_last R D F σ
  exact (heq_of_eq (dgCoherentBarBianchiData_full_equation R D F σ)).trans
    (gradedHom_compose_heq (A := R) (D := RightModule R D) hx hy hy rfl rfl rfl
      _ _ _ _ (dgCoherentBarBianchiTheta_heq R D F σ)
      (dgCoherentBarBianchiData_hom_univ_heq R D F σ) rfl rfl)

end SerrePositivity.InfinityCategories
