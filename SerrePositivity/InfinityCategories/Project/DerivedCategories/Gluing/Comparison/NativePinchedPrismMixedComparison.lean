module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativePinchedPrismMixedValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeCoefficientPrismValue

/-! 元 gluing augmentation の全実混合係数は、同じ元 Hom 上の明示 cochain prism の実係数に一致。 -/
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

lemma dgGluingNativePinchedPrism_mixed_comparison
    (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hβ : (SSet.stdSimplex.objEquiv β).toOrderHom (J.min' hJ) = 0) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
        (s.val.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (SSet.stdSimplex.objEquiv β).toOrderHom)).hom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega))
      ((_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (M.value X.left Y.right)).inv.f k
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
            (Opposite.op ⦋n⦌)
            (β, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s))).component
            J k hJ hk))) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedPrism_mixed_value R C D M s
    (SSet.stdSimplex.objEquiv β).toOrderHom J k hJ hk hβ
  have hv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeCoefficientPrism_model_component R C D M s β J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeCoefficientPrismValue, ite_eq_right (by rw [hβ]; decide)] at hv
  exact hc.trans (heq_of_eq (congrArg
    (fun z => (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k z) hv.symm))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
