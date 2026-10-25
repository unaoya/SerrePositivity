module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterSum
/-!
概要：標準面から回収した Hom の符号付き和を、実 Hom の微分先の次数で定義する。
方針：隣接する整数次数の算術輸送と合成の線形性を使う。
規約：次数の輸送を明示し、余錐の全標準面を含む。
使われ方：回収した高次 Hom の微分方程式を全 Hom の等式として公開する。
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
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

def dgCoherentBarCoconeFaceHom {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) (a : Fin (m + 2)) :
    GradedHom R (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) (-((m + 1 : ℕ) : ℤ) + 1) :=
  gradedHomTransport (A := R) (D := RightModule R D) rfl rfl
    (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega)
    (dgCoherentBarCoconeFamilyHom R D F hMC y ((coconeMappingSpace F y).δ a c))

def dgCoherentBarCoconeFamilyHomBoundary {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) :
    GradedHom R (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) (-((m + 1 : ℕ) : ℤ) + 1) :=
  ∑ a : Fin (m + 2), (((m + 1 : ℕ) : ℤ) - (a.val : ℤ)).negOnePow •
    dgCoherentBarCoconeFaceHom R D F hMC y c a

lemma dgCoherentBarCoconeFamilyHomBoundary_columns {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) :
    compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgNerve.vertexEquiv R (RightModule R D) y)
      (dgCoherentBarCoconeFamilyHomBoundary R D F hMC y c)
      (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
      (show -(n : ℤ) + (-((m + 1 : ℕ) : ℤ) + 1) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega) =
      ∑ a : Fin (m + 2), (((m + 1 : ℕ) : ℤ) - (a.val : ℤ)).negOnePow •
        dgCoherentBarCoconeFaceColumn R D F hMC y c s a := by
  unfold dgCoherentBarCoconeFamilyHomBoundary
  rw [DGNerve.compose_sum_left]
  apply Finset.sum_congr rfl
  intro a _
  rw [DGNerve.compose_units_smul_left]
  congr 1
  have hF := gradedHomTransport_heq (A := R) (D := RightModule R D) rfl rfl
    (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega)
    (dgCoherentBarCoconeFamilyHom R D F hMC y ((coconeMappingSpace F y).δ a c))
  exact eq_of_heq (gradedHom_compose_heq (A := R) (D := RightModule R D)
    (x := dgCoherentBarSource R D F ⟨n, s⟩)
    (y := dgCoherentBarNormalizedModule R D F hMC)
    (z := dgNerve.vertexEquiv R (RightModule R D) y)
    rfl rfl rfl rfl (show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by omega) rfl
    (p := -(n : ℤ)) (q := -((m + 1 : ℕ) : ℤ) + 1)
    (k := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (p' := -(n : ℤ)) (q' := -(m : ℤ)) (k' := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (dgCoherentBarCoconeFaceHom R D F hMC y c a) (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    (dgCoherentBarCoconeFamilyHom R D F hMC y ((coconeMappingSpace F y).δ a c))
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) hF HEq.rfl (by omega) (by omega))

end SerrePositivity.InfinityCategories
