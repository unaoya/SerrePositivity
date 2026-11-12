module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPrismModelComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeCochainCorrectionValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomCoefficientAugmentationHomotopy

/-! 元 dg Hom 上の同じ実明示 prism の出力を、二作用と元 primitive の係数へ厳密に戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M} {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y) _⦋n⦌)

def dgGluingNativeCoefficientPrismValue (β : Fin (n + 1) →o Fin 2)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (M.value X.left Y.right).X k :=
  if β (J.min' hJ) = 1 then
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y).f k
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)
  else (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y).f k
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk) +
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePrismCorrectionValue R C D M s β J k hk

lemma dgGluingNativeCoefficientPrism_model_component
    (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (M.value X.left Y.right)).inv.f k
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
          (Opposite.op ⦋n⦌)
          (β, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s))).component
          J k hJ hk) =
      dgGluingNativeCoefficientPrismValue R C D M s (SSet.stdSimplex.objEquiv β).toOrderHom
        J k hJ hk := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPrism_model_component.{u, max u v w} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y)
    (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomNegativePrimitive_boundary R C D M X Y)
    s β J k hJ hk
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePrismCorrectionValue_eq_cochain R C D M s _ J k hk] at hc
  exact hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
