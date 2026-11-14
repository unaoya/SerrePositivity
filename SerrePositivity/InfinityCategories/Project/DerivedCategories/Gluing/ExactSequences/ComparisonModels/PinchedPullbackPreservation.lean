module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.PinchedPullbackElements

/-! 全 Hom 複体の厳密な引き戻しは、実 pinched 写像空間の厳密な引き戻しになる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
variable {R : Type u} [CommRing R] {D₀ D₁ D₂ D₃ : Type v}
  [DGCategory R D₀] [DGCategory R D₁] [DGCategory R D₂] [DGCategory R D₃]
  {x₀ y₀ : D₀} {x₁ y₁ : D₁} {x₂ y₂ : D₂} {x₃ y₃ : D₃}
  {a : homObject R D₀ x₀ y₀ ⟶ homObject R D₁ x₁ y₁}
  {b : homObject R D₀ x₀ y₀ ⟶ homObject R D₂ x₂ y₂}
  {f : homObject R D₁ x₁ y₁ ⟶ homObject R D₃ x₃ y₃}
  {g : homObject R D₂ x₂ y₂ ⟶ homObject R D₃ x₃ y₃}

lemma dgGluingPinchedChainMap_isPullback (h : IsPullback a b f g) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap g) := by
  have hw : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap g := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp, h.w]
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app hw n, ?_, ?_⟩
  · intro s t hst
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackElement_ext h n s t hst.1 hst.2
  · intro s t hst
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackElement_exists h n s t hst

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
