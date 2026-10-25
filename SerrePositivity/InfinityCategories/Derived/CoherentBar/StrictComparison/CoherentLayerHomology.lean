module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentDimensionLayers
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexCoproductHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
概要：実 coherent bar の内部次元層のホモロジーを係数ホモロジーの直和に同定する。
方針：評価の直和保存、加群圏の AB4、整数 shift のホモロジー同型を合成する。
規約：元の coherent 図式を保ち、複体の有界性を仮定しない。
使われ方：単体次元フィルトレーションの最初のホモロジー。
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
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarLayerSummandHomologyIso (x : D) (q : ℤ) (n : ℕ)
    (s : dgCoherentBarLayerIndex I n) :
    ((moduleEvaluation R D x).obj (dgCoherentBarLayerFamily R D G n s)).homology q ≅
      ((dgCoherentBarSource R D G s.val.val).obj (Opposite.op x)).homology ((n : ℤ) + q) := by
  change ((((dgCoherentBarSource R D G s.val.val).obj
    (Opposite.op x))⟦(s.val.val.1 : ℤ)⟧).homology q) ≅ _
  exact (CochainComplex.ShiftSequence.shiftIso (ModuleCat R)
    (s.val.val.1 : ℤ) q ((n : ℤ) + q) (by rw [s.property])).app _

def dgCoherentBarLayerHomologyIso (x : D) (q : ℤ) (n : ℕ) :
    ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n)).homology q ≅
      ∐ fun s : dgCoherentBarLayerIndex I n =>
        ((dgCoherentBarSource R D G s.val.val).obj (Opposite.op x)).homology ((n : ℤ) + q) :=
  HomologicalComplex.homologyMapIso
    (PreservesCoproduct.iso (moduleEvaluation R D x) (dgCoherentBarLayerFamily R D G n)) q ≪≫
    dgComplexCoproductHomologyIso R
      (fun s => (moduleEvaluation R D x).obj (dgCoherentBarLayerFamily R D G n s)) q ≪≫
    Sigma.mapIso (dgCoherentBarLayerSummandHomologyIso R D G x q n)

end SerrePositivity.InfinityCategories
