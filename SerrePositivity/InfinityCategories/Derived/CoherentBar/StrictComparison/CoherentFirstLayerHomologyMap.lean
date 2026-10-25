module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneHomologyRepresentative

/-!
概要：実内部次元層の一次作用素によるホモロジー射。
方針：各評価で閉じた次数一 cochain を作り、隣接短複体のホモロジーへ送る。
規約：bar の元の一次列の実射を使う。
使われ方：長完全列の連結射から定義した一次微分との一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarFirstLayerCochain (x : D) (n : ℕ) :
    Cochain ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1)))
      ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n)) 1 :=
  (moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G (n + 1)))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n)) x).f 1
      (dgCoherentBarLayerFirstHom R D G n)

lemma dgCoherentBarFirstLayerCochain_closed (x : D) (n : ℕ) :
    δ 1 2 (dgCoherentBarFirstLayerCochain R D G x n) = 0 := by
  have h := moduleHomElement_d_π R D 1 2 (dgCoherentBarLayerFirstHom R D G n) x
  rw [dgCoherentBarLayerFirstHom_d, map_zero] at h
  exact h.symm

def dgCoherentBarFirstLayerHomologyMap (x : D) (q : ℤ) (n : ℕ) :
    ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).homology q ⟶
      ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n)).homology (q + 1) :=
  dgDegreeOneHomologyMap R (dgCoherentBarFirstLayerCochain R D G x n)
    (dgCoherentBarFirstLayerCochain_closed R D G x n) q

end SerrePositivity.InfinityCategories
