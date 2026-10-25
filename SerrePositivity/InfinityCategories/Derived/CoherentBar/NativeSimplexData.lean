module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedTargetProjection
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LastPostcomposition
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiEquation
/-!
概要：正規化実 bar を最後の対象とする余錐の単体データを構成する。
方針：D の Bianchi データの最後への全成分を、実正規化射影で後合成する。
規約：元の図式を先頭面に保持し、正規化加群の公開型を変更しない。
使われ方：native 余錐の全 HA 方程式と単体的自然性。
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

def dgCoherentBarNativeBianchiProjection {n : ℕ} (s : I _⦋n⦌) :
    GradedHom R ((dgCoherentBarBianchiData R D F s).obj (Fin.last (n + 1)))
      (dgCoherentBarNormalizedModule R D F hMC) 0 :=
  (gradedHomTransportWithHEq (A := R) (D := RightModule R D)
    (dgCoherentBarBianchiData_obj_last R D F s).symm rfl rfl
    (dgCoherentBarNormalizedTargetProjection R D F hMC)).val

lemma dgCoherentBarNativeBianchiProjection_heq {n : ℕ} (s : I _⦋n⦌) :
    HEq (dgCoherentBarNativeBianchiProjection R D F hMC s)
      (dgCoherentBarNormalizedTargetProjection R D F hMC) :=
  (gradedHomTransportWithHEq (A := R) (D := RightModule R D) _ _ _ _).property

lemma dgCoherentBarNativeBianchiProjection_d {n : ℕ} (s : I _⦋n⦌) :
    differential R (dgCoherentBarNativeBianchiProjection R D F hMC s) =
    compose R (x := (dgCoherentBarBianchiData R D F s).obj (Fin.last (n + 1)))
      (y := (dgCoherentBarBianchiData R D F s).obj (Fin.last (n + 1)))
      (z := dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarNativeBianchiProjection R D F hMC s)
      (dgCoherentBarBianchiTheta R D F s) (add_zero 1) := by
  have hx := dgCoherentBarBianchiData_obj_last R D F s
  have hρ := dgCoherentBarNativeBianchiProjection_heq R D F hMC s
  have hd := gradedHom_differential_heq (A := R) (D := RightModule R D)
    hx rfl rfl _ _ hρ
  have hc := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hx rfl rfl rfl rfl _ _ _ _ hρ (dgCoherentBarBianchiTheta_heq R D F s)
    (add_zero 1) (add_zero 1)
  exact eq_of_heq (hd.trans ((heq_of_eq
    (dgCoherentBarNormalizedTargetProjection_d R D F hMC)).trans hc.symm))

def dgCoherentBarNativeSimplexData {n : ℕ} (s : I _⦋n⦌) :
    SimplexData R (RightModule R D) (n + 1) :=
  dgCoherentBarPostLastData (dgCoherentBarBianchiData R D F s)
    (dgCoherentBarNormalizedModule R D F hMC)
    (dgCoherentBarNativeBianchiProjection R D F hMC s)

lemma dgCoherentBarNativeSimplexData_front {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarNativeSimplexData R D F hMC s).pullback Fin.castSuccOrderEmb.toOrderHom =
      (coherentDiagramSimplex F s).toSimplexData := by
  rw [dgCoherentBarNativeSimplexData, dgCoherentBarPostLastData_front,
    dgCoherentBarBianchiData_front]

lemma dgCoherentBarNativeSimplexData_last_equation {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    differential R ((dgCoherentBarNativeSimplexData R D F hMC s).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk) =
    (dgCoherentBarNativeSimplexData R D F hMC s).rhs
      J a (Fin.last (n + 1)) k hJ ha hb hk :=
  dgCoherentBarPostLastData_equation_last (dgCoherentBarBianchiData R D F s)
    (dgCoherentBarNormalizedModule R D F hMC)
    (dgCoherentBarNativeBianchiProjection R D F hMC s) (dgCoherentBarBianchiTheta R D F s)
    (dgCoherentBarNativeBianchiProjection_d R D F hMC s) J a k hJ ha hb hk
    (dgCoherentBarBianchiData_last_hom_d R D F s J a k hJ ha hb hk)
    (dgCoherentBarBianchiData_rhs R D F s J a k hJ ha hb hk)

end SerrePositivity.InfinityCategories
