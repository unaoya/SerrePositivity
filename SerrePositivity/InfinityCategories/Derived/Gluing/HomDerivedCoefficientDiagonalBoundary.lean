module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientDiagonalHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalUncurryHomotopyBoundary

/-! 元の二対角を結ぶ同じ実ホモトピーは、元の導来始終点を全時刻で固定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedCoefficientDiagonalHomotopy_source (X Y : DGGluingObject R C D M) :
    (prismEndpoint 0 _ ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y).h =
      SSet.const ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) := by
  rw [dgGluingUniverseDerivedYoneda_vertex R C X.left]
  exact dgGluingIntervalUncurryHomotopy_source
    (dgGluingHomDerivedCoefficientIntervalHomotopy R C D M X Y)

lemma dgGluingHomDerivedCoefficientDiagonalHomotopy_target (X Y : DGGluingObject R C D M) :
    (prismEndpoint 1 _ ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y).h =
      SSet.const ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))) := by
  rw [dgGluingUniverseDerivedCoefficient_vertex R C D M Y.right]
  exact dgGluingIntervalUncurryHomotopy_target
    (dgGluingHomDerivedCoefficientIntervalHomotopy R C D M X Y)

end SerrePositivity.InfinityCategories
