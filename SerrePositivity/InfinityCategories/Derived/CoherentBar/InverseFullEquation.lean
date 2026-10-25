module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseFullCoefficient
/-!
概要：任意の pinched 線形単体から逆構成したデータは、全頂点集合の HA 方程式を満たす。
方針：微分の Leibniz 則を、元の単体側とパラメーター側の有限和に照合する。
規約：零パラメーター次数も含み、全部分集合の方程式は後続で回収する。
使われ方：逆比較の実 HA 単体を構成する中間方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseFullColumn_differential {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    differential R (dgCoherentBarInverseFullColumn R D F hMC N f s) =
      compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
        (y := dgCoherentBarNormalizedModule R D F hMC) (z := N)
        (differential R (dgCoherentBarInverseFullHom R D F hMC N f))
        (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
        (show -(n : ℤ) + (-(m : ℤ) + 1) = -((n + m : ℕ) : ℤ) + 1 by omega) +
      (-(m : ℤ)).negOnePow •
        compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
          (y := dgCoherentBarNormalizedModule R D F hMC) (z := N)
          (dgCoherentBarInverseFullHom R D F hMC N f)
          (differential R (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩))
          (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega) := by
  unfold dgCoherentBarInverseFullColumn
  rw [differential_compose]

lemma dgCoherentBarInverse_parameter_differential_sum {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    HEq (∑ j : Fin m, dgCoherentBarFullTerm
      (dgCoherentBarInverseRawData R D F hMC N f.val s) (j.natAdd n))
      (compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
        (y := dgCoherentBarNormalizedModule R D F hMC) (z := N)
        (differential R (dgCoherentBarInverseFullHom R D F hMC N f.val))
        (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
        (show -(n : ℤ) + (-(m : ℤ) + 1) = -((n + m : ℕ) : ℤ) + 1 by omega)) := by
  cases m with
  | zero =>
    rw [dgCoherentBarInverseFullHom_closed_zero, DGNerve.zero_compose, Fin.sum_univ_zero]
    exact gradedHom_zero_heq (A := R) (D := RightModule R D)
      (dgCoherentBarInverseRawData_source R D F hMC N f.val s)
      (dgCoherentBarInverseRawData_target R D F hMC N f.val s) rfl
  | succ m =>
    rw [dgCoherentBarInverseFullHom_differential, dgCoherentBarInverseBoundary_columns]
    exact dgCoherentBarInverse_parameter_sum R D F hMC N f.val s

lemma dgCoherentBarInverseRawData_full_equation {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    differential R ((dgCoherentBarInverseRawData R D F hMC N f.val s).hom Finset.univ
      0 (Fin.last (n + m + 1)) (-((n + m : ℕ) : ℤ))
      (coherentDiagramTop_card (n + m)) (coherentDiagramTop_min (n + m))
      (coherentDiagramTop_max (n + m)) (by simp; omega)) =
    (dgCoherentBarInverseRawData R D F hMC N f.val s).rhs Finset.univ
      0 (Fin.last (n + m + 1)) (-((n + m : ℕ) : ℤ))
      (coherentDiagramTop_card (n + m)) (coherentDiagramTop_min (n + m))
      (coherentDiagramTop_max (n + m)) (by simp; omega) := by
  have hx := dgCoherentBarInverseRawData_source R D F hMC N f.val s
  have hz := dgCoherentBarInverseRawData_target R D F hMC N f.val s
  have hD := gradedHom_differential_heq (A := R) (D := RightModule R D) hx hz rfl _ _
    (dgCoherentBarInverseRawData_full_hom_heq R D F hMC N f.val s)
  rw [dgCoherentBarInverseFullColumn_differential, Int.negOnePow_neg] at hD
  rw [dgCoherentBarFullSimplex_rhs_split]
  have hS := dgCoherentBarInverse_source_sum R D F hMC N f.val s
  have hP := dgCoherentBarInverse_parameter_differential_sum R D F hMC N f s
  have hAdd := gradedHom_add_heq (A := R) (D := RightModule R D) hx hz rfl
    _ _ _ _ hS hP
  exact eq_of_heq (hD.trans ((heq_of_eq (add_comm _ _)).trans hAdd.symm))

end SerrePositivity.InfinityCategories
