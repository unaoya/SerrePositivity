module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredParameterTerm
/-!
概要：回収した一点下のデータは、全頂点集合の実 HA 方程式を満たす。
方針：回収 Hom の微分式を全 HA 項との比較で移し、零次元では閉性を使う。
規約：全部分集合への方程式の移送は後続で行う。
使われ方：標準 Hom の持ち上げの高次補正を実一点下の単体へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgCoherentBarHom_sum_heq_of_degree {A : Type u} [CommRing A]
    {C : Type v} [DGCategory A C] {a b a' b' : C} {k l : ℤ}
    {ι : Type*} [Fintype ι] (ha : a = a') (hb : b = b') (hk : k = l)
    (f : ι → GradedHom A a b k) (g : ι → GradedHom A a' b' l)
    (h : ∀ i, HEq (f i) (g i)) : HEq (∑ i, f i) (∑ i, g i) := by
  cases ha
  cases hb
  cases hk
  apply heq_of_eq
  apply Finset.sum_congr rfl
  intro i _
  exact eq_of_heq (h i)

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecovered_parameter_sum {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) :
    HEq (∑ j : Fin (m + 1), dgCoherentBarFullTerm
      (dgCoherentBarCoconeRecoveredRawData R D F hMC c) (j.natAdd 0))
      (∑ j : Fin (m + 1), dgCoherentBarCoconeLiftParameterTerm R D F hMC c j) :=
  dgCoherentBarHom_sum_heq_of_degree (dgCoherentBarCoconeRecoveredRawData_source R D F hMC c)
    (dgCoherentBarCoconeRecoveredRawData_target R D F hMC c)
    (show -((0 + (m + 1) : ℕ) : ℤ) + 1 = -(m : ℤ) by omega)
    (fun j : Fin (m + 1) => dgCoherentBarFullTerm
      (dgCoherentBarCoconeRecoveredRawData R D F hMC c) (j.natAdd 0))
    (fun j : Fin (m + 1) => dgCoherentBarCoconeLiftParameterTerm R D F hMC c j)
    (fun j => dgCoherentBarCoconeRecoveredFullTerm_parameter R D F hMC c j)

lemma dgCoherentBarCoconeRecoveredRawData_full_equation {n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) :
    differential R ((dgCoherentBarCoconeRecoveredRawData R D F hMC c).hom Finset.univ
      0 (Fin.last (0 + n + 1)) (-((0 + n : ℕ) : ℤ))
      (coherentDiagramTop_card (0 + n)) (coherentDiagramTop_min (0 + n))
      (coherentDiagramTop_max (0 + n)) (by simp; omega)) =
    (dgCoherentBarCoconeRecoveredRawData R D F hMC c).rhs Finset.univ
      0 (Fin.last (0 + n + 1)) (-((0 + n : ℕ) : ℤ))
      (coherentDiagramTop_card (0 + n)) (coherentDiagramTop_min (0 + n))
      (coherentDiagramTop_max (0 + n)) (by simp; omega) := by
  let Q := dgCoherentBarCoconeRecoveredRawData R D F hMC c
  have hx := dgCoherentBarCoconeRecoveredRawData_source R D F hMC c
  have hz := dgCoherentBarCoconeRecoveredRawData_target R D F hMC c
  have hFull : HEq (Q.hom Finset.univ 0 (Fin.last (0 + n + 1)) (-((0 + n : ℕ) : ℤ))
      (coherentDiagramTop_card (0 + n)) (coherentDiagramTop_min (0 + n))
      (coherentDiagramTop_max (0 + n)) (by simp; omega))
      (dgCoherentBarCoconeLiftHom R D F hMC c) :=
    (SimplexData.hom_heq_of_indices_degree Q rfl rfl rfl (by omega)).trans
      (dgCoherentBarCoconeRecoveredRawData_full_hom_heq R D F hMC c)
  have hD := gradedHom_differential_heq (A := R) (D := RightModule R D)
    hx hz (show -((0 + n : ℕ) : ℤ) = -(n : ℤ) by omega) _ _ hFull
  rw [dgCoherentBarFullSimplex_rhs_split, Fin.sum_univ_zero]
  rw [zero_add (∑ j : Fin n, dgCoherentBarFullTerm Q (j.natAdd 0))]
  cases n with
  | zero =>
    have hClosed : differential R (x := dgCoherentBarNormalizedModule R D F hMC)
        (y := dgCoherentBarCoconeLiftTarget R D F c)
        (dgCoherentBarCoconeLiftHom R D F hMC c) = 0 :=
      dgCoherentBarCoconeLiftHom_closed_zero R D F hMC c
    rw [hClosed] at hD
    rw [Fin.sum_univ_zero]
    exact eq_of_heq (hD.trans (gradedHom_zero_heq (A := R) (D := RightModule R D)
      hx.symm hz.symm rfl))
  | succ m =>
    exact eq_of_heq (hD.trans
      ((dgCoherentBarCoconeLiftHom_parameter_differential R D F hMC c).trans
        (dgCoherentBarCoconeRecovered_parameter_sum R D F hMC c).symm))

end SerrePositivity.InfinityCategories
