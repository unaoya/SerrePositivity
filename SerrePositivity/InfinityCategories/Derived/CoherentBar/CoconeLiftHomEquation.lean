module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterTerm
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftResidual
/-!
概要：動く右面を持つ余錐族から回収した Hom の全微分方程式を証明する。
方針：源側相殺とパラメーター項の因数分解を合わせ、native 成分同値の単射性を使う。
規約：右面の非線形な切断合成を全て保持する。
使われ方：標準 Hom の持ち上げの高次補正を実 HA 単体へ組み立てる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
private lemma lifted_compose_zero_of_degree {R : Type u} [CommRing R]
    {C : Type v} [DGCategory R C] {a b c : C} {p q k l : ℤ}
    (g : GradedHom R b c q) (f : GradedHom R a b p)
    (hk : p + q = k) (hl : p + q = l) (h : compose R g f hk = 0) :
    compose R g f hl = 0 := by
  have he : k = l := hk.symm.trans hl
  cases he
  exact h

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeLift_parameter_sum {m n : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (s : I _⦋n⦌) :
    HEq (∑ j : Fin (m + 1), dgCoherentBarFullTerm
      (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (j.natAdd n))
      (compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := dgCoherentBarCoconeLiftTarget R D F c)
        (∑ j : Fin (m + 1), dgCoherentBarCoconeLiftParameterTerm R D F hMC c j)
        (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
        (show -(n : ℤ) + -(m : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)) := by
  have h := sum_heq_of_obj_eq
    (dgCoherentBarCoconeLiftSimplex_source R D F c s)
    (dgCoherentBarCoconeLiftSimplex_target R D F c s)
    (fun j : Fin (m + 1) => dgCoherentBarFullTerm
      (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (j.natAdd n))
    (fun j : Fin (m + 1) => compose R
      (x := dgCoherentBarSource R D F ⟨n, s⟩)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgCoherentBarCoconeLiftTarget R D F c)
      (dgCoherentBarCoconeLiftParameterTerm R D F hMC c j)
      (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
      (show -(n : ℤ) + -(m : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega))
    (fun j => dgCoherentBarCoconeLiftFullTerm_parameter R D F hMC c s j)
  rw [← DGNerve.compose_sum_left] at h
  exact h

lemma dgCoherentBarCoconeLiftHom_parameter_differential {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) :
    HEq (differential R (x := dgCoherentBarNormalizedModule R D F hMC)
      (y := dgCoherentBarCoconeLiftTarget R D F c) (dgCoherentBarCoconeLiftHom R D F hMC c))
      (∑ j : Fin (m + 1), dgCoherentBarCoconeLiftParameterTerm R D F hMC c j) := by
  apply dgCoherentBarNativeHom_heq_of_columns R D F hMC
    (N := dgCoherentBarCoconeLiftTarget R D F c)
    (N' := dgCoherentBarCoconeLiftTarget R D F c)
    (q := -((m + 1 : ℕ) : ℤ) + 1) (q' := -(m : ℤ)) rfl (by omega)
  intro s
  have hDegreeL := dgCoherentBarHom_compose_degree_heq (R := R) (C := RightModule R D)
    (a := dgCoherentBarSource R D F s.val)
    (b := dgCoherentBarNormalizedModule R D F hMC)
    (c := dgCoherentBarCoconeLiftTarget R D F c)
    (p := -(s.val.1 : ℤ)) (q := -((m + 1 : ℕ) : ℤ) + 1)
    (k := (-((m + 1 : ℕ) : ℤ) + 1) - (s.val.1 : ℤ))
    (l := -((m + 1 : ℕ) : ℤ) - (s.val.1 : ℤ) + 1)
    (differential R (x := dgCoherentBarNormalizedModule R D F hMC)
      (y := dgCoherentBarCoconeLiftTarget R D F c) (dgCoherentBarCoconeLiftHom R D F hMC c))
    (dgCoherentBarNativeColumn R D F hMC s.val) (by omega) (by omega)
  have hDegreeR := dgCoherentBarHom_compose_degree_heq (R := R) (C := RightModule R D)
    (a := dgCoherentBarSource R D F s.val)
    (b := dgCoherentBarNormalizedModule R D F hMC)
    (c := dgCoherentBarCoconeLiftTarget R D F c)
    (p := -(s.val.1 : ℤ)) (q := -(m : ℤ))
    (k := -((s.val.1 + (m + 1) : ℕ) : ℤ) + 1)
    (l := -(m : ℤ) - (s.val.1 : ℤ))
    (∑ j : Fin (m + 1), dgCoherentBarCoconeLiftParameterTerm R D F hMC c j)
    (dgCoherentBarNativeColumn R D F hMC s.val) (by omega) (by omega)
  exact hDegreeL.trans
    ((dgCoherentBarCoconeLiftHom_d_column_residual R D F hMC c s.val.2).trans
      ((dgCoherentBarCoconeLift_parameter_sum R D F hMC c s.val.2).trans hDegreeR))

lemma dgCoherentBarCoconeLiftHom_closed_zero
    (c : (sliceUnder F) _⦋0⦌) :
    (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarCoconeLiftTarget R D F c)).d 0 1
      (dgCoherentBarCoconeLiftHom R D F hMC c) = 0 := by
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgCoherentBarCoconeLiftTarget R D F c) 1).injective
  rw [map_zero]
  funext s
  rw [Pi.zero_apply, ← dgCoherentBarNativeColumn_compose_eq_coordinates]
  have h := dgCoherentBarCoconeLiftHom_d_column_residual R D F hMC c s.val.2
  simp only [Fin.sum_univ_zero] at h
  have hZero := gradedHom_zero_heq (A := R) (D := RightModule R D)
    (k := -((s.val.1 + 0 : ℕ) : ℤ) + 1) (l := -(0 : ℤ) - (s.val.1 : ℤ) + 1)
    (dgCoherentBarCoconeLiftSimplex_source R D F c s.val.2)
    (dgCoherentBarCoconeLiftSimplex_target R D F c s.val.2) (by omega)
  have hCol := eq_of_heq (h.trans hZero)
  exact lifted_compose_zero_of_degree _ _
    (show -(s.val.1 : ℤ) + 1 = -(0 : ℤ) - (s.val.1 : ℤ) + 1 by omega)
    (by omega) hCol

end SerrePositivity.InfinityCategories
