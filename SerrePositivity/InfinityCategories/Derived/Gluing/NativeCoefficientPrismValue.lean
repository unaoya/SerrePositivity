module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPrismModelComponent
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCochainCorrectionValue
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientAugmentationHomotopy

/-! 元 dg Hom 上の同じ実明示 prism の出力を、二作用と元 primitive の係数へ厳密に戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

def dgGluingNativeCoefficientPrismValue (β : Fin (n + 1) →o Fin 2)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (M.value X.left Y.right).X k :=
  if β (J.min' hJ) = 1 then
    (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y).f k
      ((toLinearData s).component J k hJ hk)
  else (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y).f k
      ((toLinearData s).component J k hJ hk) +
    dgGluingNativePrismCorrectionValue R C D M s β J k hk

lemma dgGluingNativeCoefficientPrism_model_component
    (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (complexUnitHomIso (M.value X.left Y.right)).inv.f k
        ((toLinearData ((dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
          (Opposite.op ⦋n⦌)
          (β, (pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s))).component
          J k hJ hk) =
      dgGluingNativeCoefficientPrismValue R C D M s (SSet.stdSimplex.objEquiv β).toOrderHom
        J k hJ hk := by
  have hc := dgGluingComplexPrism_model_component.{u, max u v w} R (DGGluingObject R C D M)
    (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y)
    (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y)
    (-dgGluingHomPrimitive R C D M X Y) (dgGluingHomNegativePrimitive_boundary R C D M X Y)
    s β J k hJ hk
  rw [← dgGluingNativePrismCorrectionValue_eq_cochain R C D M s _ J k hk] at hc
  exact hc

end SerrePositivity.InfinityCategories
