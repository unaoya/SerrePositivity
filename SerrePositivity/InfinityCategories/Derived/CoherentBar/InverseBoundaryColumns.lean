module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterSum
/-!
概要：逆構成の標準面から回収した Hom の符号付き和を、実 Hom の微分先の次数で定義する。
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
  (N : RightModule R D)

def dgCoherentBarInverseBoundaryFaceHom {m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (a : Fin (m + 2)) :
    GradedHom R (dgCoherentBarNormalizedModule R D F hMC)
      (N) (-((m + 1 : ℕ) : ℤ) + 1) :=
  gradedHomTransport (A := R) (D := RightModule R D) rfl rfl
    (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega)
    (dgCoherentBarInverseFaceHom R D F hMC N f a)

def dgCoherentBarInverseBoundary {m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1)) :
    GradedHom R (dgCoherentBarNormalizedModule R D F hMC)
      (N) (-((m + 1 : ℕ) : ℤ) + 1) :=
  ∑ a : Fin (m + 2), (((m + 1 : ℕ) : ℤ) - (a.val : ℤ)).negOnePow •
    dgCoherentBarInverseBoundaryFaceHom R D F hMC N f a

lemma dgCoherentBarInverseBoundary_columns {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) :
    compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := N)
      (dgCoherentBarInverseBoundary R D F hMC N f)
      (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
      (show -(n : ℤ) + (-((m + 1 : ℕ) : ℤ) + 1) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega) =
      ∑ a : Fin (m + 2), (((m + 1 : ℕ) : ℤ) - (a.val : ℤ)).negOnePow •
        dgCoherentBarInverseFaceColumn R D F hMC N f s a := by
  unfold dgCoherentBarInverseBoundary
  rw [DGNerve.compose_sum_left]
  apply Finset.sum_congr rfl
  intro a _
  rw [DGNerve.compose_units_smul_left]
  congr 1
  have hF := gradedHomTransport_heq (A := R) (D := RightModule R D) rfl rfl
    (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega)
    (dgCoherentBarInverseFaceHom R D F hMC N f a)
  exact eq_of_heq (gradedHom_compose_heq (A := R) (D := RightModule R D)
    (x := dgCoherentBarSource R D F ⟨n, s⟩)
    (y := dgCoherentBarNormalizedModule R D F hMC)
    (z := N)
    rfl rfl rfl rfl (show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by omega) rfl
    (p := -(n : ℤ)) (q := -((m + 1 : ℕ) : ℤ) + 1)
    (k := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (p' := -(n : ℤ)) (q' := -(m : ℤ)) (k' := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (dgCoherentBarInverseBoundaryFaceHom R D F hMC N f a)
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    (dgCoherentBarInverseFaceHom R D F hMC N f a)
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) hF HEq.rfl (by omega) (by omega))

end SerrePositivity.InfinityCategories
