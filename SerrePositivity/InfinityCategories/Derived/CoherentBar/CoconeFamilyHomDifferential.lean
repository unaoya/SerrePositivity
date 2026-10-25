module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyResidual
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyBoundary
/-!
概要：余錐族から回収した高次 Hom の実微分は、全標準面の符号付き境界と一致する。
方針：混合 HA 方程式の残差とパラメーター和を合わせ、native 成分同値の単射性を使う。
規約：零次元では実閉性を、正次数では全 Hom の等式を結論する。
使われ方：写像空間の高次逆構成の微分方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

private lemma compose_eq_of_degree {R : Type u} [CommRing R]
    {C : Type v} [DGCategory R C] {a b c : C} {p q k l : ℤ}
    (g g' : GradedHom R b c q) (f : GradedHom R a b p)
    (hk : p + q = k) (hl : p + q = l) (h : compose R g f hk = compose R g' f hk) :
    compose R g f hl = compose R g' f hl := by
  have he : k = l := hk.symm.trans hl
  cases he
  exact h

private lemma compose_zero_of_degree {R : Type u} [CommRing R]
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
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamilyHom_d_columns {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) :
    compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgNerve.vertexEquiv R (RightModule R D) y)
      (differential R (dgCoherentBarCoconeFamilyHom R D F hMC y c))
      (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
      (show -(n : ℤ) + (-((m + 1 : ℕ) : ℤ) + 1) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega) =
    compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgNerve.vertexEquiv R (RightModule R D) y)
      (dgCoherentBarCoconeFamilyHomBoundary R D F hMC y c)
      (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
      (show -(n : ℤ) + (-((m + 1 : ℕ) : ℤ) + 1) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega) := by
  have hCast := dgCoherentBarHom_compose_degree_heq (R := R)
    (a := dgCoherentBarSource R D F ⟨n, s⟩) (b := dgCoherentBarNormalizedModule R D F hMC)
    (c := dgNerve.vertexEquiv R (RightModule R D) y)
    (p := -(n : ℤ)) (q := -((m + 1 : ℕ) : ℤ) + 1)
    (k := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (l := -((m + 1 : ℕ) : ℤ) - (n : ℤ) + 1)
    (differential R (dgCoherentBarCoconeFamilyHom R D F hMC y c))
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) (by omega) (by omega)
  exact eq_of_heq (hCast.trans
    ((dgCoherentBarCoconeFamilyHom_d_column_residual R D F hMC y c s).trans
      ((dgCoherentBarCoconeFamily_parameter_sum R D F hMC y c s).trans
        (heq_of_eq (dgCoherentBarCoconeFamilyHomBoundary_columns R D F hMC y c s).symm))))

lemma dgCoherentBarCoconeFamilyHom_differential {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) :
    differential R (x := dgCoherentBarNormalizedModule R D F hMC)
      (y := dgNerve.vertexEquiv R (RightModule R D) y)
      (dgCoherentBarCoconeFamilyHom R D F hMC y c) =
      dgCoherentBarCoconeFamilyHomBoundary R D F hMC y c := by
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgNerve.vertexEquiv R (RightModule R D) y) (-((m + 1 : ℕ) : ℤ) + 1)).injective
  funext s
  rw [← dgCoherentBarNativeColumn_compose_eq_coordinates,
    ← dgCoherentBarNativeColumn_compose_eq_coordinates]
  exact compose_eq_of_degree _ _ _
    (show -(s.val.1 : ℤ) + (-((m + 1 : ℕ) : ℤ) + 1) =
      -((s.val.1 + (m + 1) : ℕ) : ℤ) + 1 by omega)
    (by omega) (dgCoherentBarCoconeFamilyHom_d_columns R D F hMC y c s.val.2)

lemma dgCoherentBarCoconeFamilyHom_closed_zero
    (c : (coconeMappingSpace F y) _⦋0⦌) :
    (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y)).d 0 1
      (dgCoherentBarCoconeFamilyHom R D F hMC y c) = 0 := by
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgNerve.vertexEquiv R (RightModule R D) y) 1).injective
  rw [map_zero]
  funext s
  rw [Pi.zero_apply, ← dgCoherentBarNativeColumn_compose_eq_coordinates]
  have h := dgCoherentBarCoconeFamilyHom_d_column_residual R D F hMC y c s.val.2
  simp only [Fin.sum_univ_zero] at h
  have hZero := gradedHom_zero_heq (A := R) (D := RightModule R D)
    (k := -((s.val.1 + 0 : ℕ) : ℤ) + 1) (l := -(0 : ℤ) - (s.val.1 : ℤ) + 1)
    (dgCoherentBarCoconeFamilySimplex_source R D F y c s.val.2)
    (dgCoherentBarCoconeFamilySimplex_target R D F y c s.val.2) (by omega)
  have hCol := eq_of_heq (h.trans hZero)
  exact compose_zero_of_degree _ _
    (show -(s.val.1 : ℤ) + 1 = -(0 : ℤ) - (s.val.1 : ℤ) + 1 by omega)
    (by omega) hCol

end SerrePositivity.InfinityCategories
