module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPullbackElements

/-! 全 Hom 複体の厳密な引き戻しは、実 pinched 写像空間の厳密な引き戻しになる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
variable {R : Type u} [CommRing R] {D₀ D₁ D₂ D₃ : Type v}
  [DGCategory R D₀] [DGCategory R D₁] [DGCategory R D₂] [DGCategory R D₃]
  {x₀ y₀ : D₀} {x₁ y₁ : D₁} {x₂ y₂ : D₂} {x₃ y₃ : D₃}
  {a : homObject R D₀ x₀ y₀ ⟶ homObject R D₁ x₁ y₁}
  {b : homObject R D₀ x₀ y₀ ⟶ homObject R D₂ x₂ y₂}
  {f : homObject R D₁ x₁ y₁ ⟶ homObject R D₃ x₃ y₃}
  {g : homObject R D₂ x₂ y₂ ⟶ homObject R D₃ x₃ y₃}

lemma dgGluingPinchedChainMap_isPullback (h : IsPullback a b f g) :
    IsPullback (pinchedHomChainMap a) (pinchedHomChainMap b)
      (pinchedHomChainMap f) (pinchedHomChainMap g) := by
  have hw : pinchedHomChainMap a ≫ pinchedHomChainMap f =
      pinchedHomChainMap b ≫ pinchedHomChainMap g := by
    rw [← pinchedHomChainMap_comp, ← pinchedHomChainMap_comp, h.w]
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app hw n, ?_, ?_⟩
  · intro s t hst
    exact dgGluingPinchedPullbackElement_ext h n s t hst.1 hst.2
  · intro s t hst
    exact dgGluingPinchedPullbackElement_exists h n s t hst

end SerrePositivity.InfinityCategories
