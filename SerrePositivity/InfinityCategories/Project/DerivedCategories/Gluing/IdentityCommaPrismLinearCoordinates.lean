module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaPinchedPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaPrismZeroCoefficient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FunctorPinchedSimplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! 明示 prism の全線形成分を、同じ二射影と元の混合係数へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  {x y : E} {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)) _⦋n⦌)
  (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))

lemma dgGluingIdentityCommaPrism_component_one
    (β : Fin (n + 1) →o Fin 2) (hβ : β (J.min' hJ) = 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component J k hJ hk =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)).f k
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk) := by
  apply eq_of_heq
  have ho := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R E s β)
    J k hJ hk
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_one R E E (DGFunctor.id E) s.val.toSimplexData
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc β _).trans hβ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_last β)
  exact ho.trans (hp.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctor_map_component_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj s (J.min' hJ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq s J k hJ hk).symm))

lemma dgGluingIdentityCommaPrism_main_component :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismMainCoefficient R E E (DGFunctor.id E) s.val.toSimplexData
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)).f k
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrismMain_target R E s.val.toSimplexData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
    (J.min' hJ).castSucc (Fin.last (n + 1)) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega) y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctor_map_component_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj s (J.min' hJ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s) k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq s J k hJ hk).symm)

lemma dgGluingIdentityCommaPrism_component_mixed
    (β : Fin (n + 1) →o Fin 2) (hβ : β (J.min' hJ) = 0) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component J k hJ hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R E E (DGFunctor.id E) s.val.toSimplexData
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R E s β)
    J k hJ hk).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E)
      s.val.toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc
      (Fin.last (n + 1)) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc β _).trans hβ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_last β))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
