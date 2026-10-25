module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyComplex
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarSplitting

/-!
概要：実一次ホモロジー複体の各対象と非退化ホモロジー bar の各対象の同型。
方針：層の内部ホモロジーを再添字付けし、総次数を固定する。
規約：この葉では対象同型のみを主張し、微分の可換性は別に検証する。
使われ方：全 coherent 入力についての一次微分の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

def dgCoherentBarFirstHomologyObjectIso (x : D) (r : ℤ) (n : ℕ) :
    (dgCoherentBarFirstHomologyComplex R D G x r).X n ≅
      (dgHomologyBarNondegComplex R (dgCoherentBarHomologyDiagram R D G x r)).X n := by
  have h : (n : ℤ) + (r - (n : ℤ)) = r := by omega
  simpa only [h] using! dgCoherentBarLayerHomologyCoefficientsIso R D G x (r - (n : ℤ)) n

end SerrePositivity.InfinityCategories
