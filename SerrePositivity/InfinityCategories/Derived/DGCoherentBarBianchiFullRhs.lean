module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiTermComparison
public import SerrePositivity.InfinityCategories.DGNerve.PinchedRhs

/-!
概要：末端に bar を加えた正次元の全体 HA 右辺は、元の θ と包含の合成に一致する。
方針：内部頂点ごとの実係数比較を有限和へ戻し、元の列の作用式を適用する。
規約：MC 方程式や余錐の普遍性を仮定しない。
使われ方：任意の部分集合へ制限して、Bianchi による bar の MC を結論する。
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

lemma dgCoherentBarBianchiData_full_rhs_heq_boundary {n : ℕ} (σ : I _⦋n + 1⦌) :
    HEq ((dgCoherentBarBianchiData R D F σ).rhs Finset.univ 0 (Fin.last (n + 2))
      (-((n + 1 : ℕ) : ℤ)) (coherentDiagramTop_card (n + 1))
      (coherentDiagramTop_min (n + 1)) (coherentDiagramTop_max (n + 1)) (by simp; omega))
      (dgCoherentBarUnshiftedBoundary R D F σ) := by
  rw [dgCoherentBarBianchiData_full_rhs_sum]
  have hx : (dgCoherentBarBianchiData R D F σ).obj 0 =
      dgCoherentBarSource R D F ⟨n + 1, σ⟩ :=
    (dgCoherentBarBianchiData_obj_castSucc R D F σ 0).trans
      (coherentDiagramSimplex_obj F σ 0)
  have hy := dgCoherentBarBianchiData_obj_last R D F σ
  exact (sum_heq_of_obj_eq (A := R) (D := RightModule R D) hx hy
    (dgCoherentBarBianchiFullTerm R D F σ) (dgCoherentBarUnshiftedBoundaryTerm R D F σ)
    (dgCoherentBarBianchiFullTerm_heq_boundaryTerm R D F σ)).trans
    (heq_of_eq (dgCoherentBarUnshiftedBoundary_eq_sum_terms R D F σ).symm)

lemma dgCoherentBarBianchiData_full_rhs_heq_theta {n : ℕ} (σ : I _⦋n + 1⦌) :
    HEq ((dgCoherentBarBianchiData R D F σ).rhs Finset.univ 0 (Fin.last (n + 2))
      (-((n + 1 : ℕ) : ℤ)) (coherentDiagramTop_card (n + 1))
      (coherentDiagramTop_min (n + 1)) (coherentDiagramTop_max (n + 1)) (by simp; omega))
      (compose R (x := dgCoherentBarSource R D F ⟨n + 1, σ⟩)
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarShiftedInclusion R D F ⟨n + 1, σ⟩) rfl) :=
  (dgCoherentBarBianchiData_full_rhs_heq_boundary R D F σ).trans
    (heq_of_eq (dgCoherentBarTheta_comp_shiftedInclusion_positive R D F σ).symm)

end SerrePositivity.InfinityCategories
