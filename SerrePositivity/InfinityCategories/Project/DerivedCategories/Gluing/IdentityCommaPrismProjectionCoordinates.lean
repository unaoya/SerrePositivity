module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaPrismLinearCorrection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPrismCorrectionEdge

/-! 同じ入力上で二射影が一致し primitive が消えれば、明示 prism の全係数は時間に定値。 -/
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
  {Q : _root_.SerrePositivity.DifferentialGraded.Complex R} (q : _root_.SerrePositivity.DifferentialGraded.homObject R E x y ⟶ Q)
  (hprim : ∀ J p hJ hp,
    q.f (p - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J p hJ hp)) = 0)
  (hpair : ∀ J k hJ hk,
    q.f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaSourceComponent R E s J k hJ hk) =
      q.f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementComponent R E s J k hJ hk))

include hprim hpair in
lemma dgGluingIdentityCommaPrism_component_post_zero
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    q.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component
        J k hJ hk) = q.f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementComponent R E s J k hJ hk) := by
  have hf : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases hf (β (J.min' hJ)) with hzero | hone
  · by_cases hJ₂ : 2 ≤ J.card
    · by_cases hsecond : β (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ₂) = 1
      · have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_correction R E s β J hJ₂ k hk
          hzero hsecond
        have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexMap_zero_of_scalar_heq q (by omega) _ _ _ hd
          (hprim (J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ₂))) (k + 1) _ _)
        rw [map_sub] at hz
        exact sub_eq_zero.mp hz
      · have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPinchedPrismCorrectionSum_second R E E (DGFunctor.id E) s
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β) J hJ₂ k hk
        rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc, ite_eq_right hsecond] at hs
        exact congrArg (fun z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k => q.f k z)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_of_correction_zero R E s β J k hJ hk hzero hs)
    · have hc : J.card = 1 := by have := Finset.card_pos.mpr hJ; omega
      have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismCorrectionSum_card_two R E E (DGFunctor.id E)
        s.val.toSimplexData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc
        (Fin.last (n + 1)) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast, hc])
      exact congrArg (fun z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k => q.f k z)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_of_correction_zero R E s β J k hJ hk hzero hs)
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_one R E s J k hJ hk β hone]
    exact hpair J k hJ hk

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
