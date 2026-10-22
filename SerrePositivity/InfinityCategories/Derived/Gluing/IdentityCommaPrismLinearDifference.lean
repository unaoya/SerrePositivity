module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismLinearCoordinates

/-! 相零の実出力と replacement 入力の全線形成分の差は、同じ実混合補正和そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  {x y : E} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) _⦋n⦌)

abbrev dgGluingIdentityCommaReplacementComponent
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom R x y k :=
  ((dgCommaAugmentationSource R E E (DGFunctor.id E)).map
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)).f k
      ((toLinearData s).component J k hJ hk)

abbrev dgGluingIdentityCommaSourceComponent
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom R x y k :=
  ((dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)).f k
      ((toLinearData s).component J k hJ hk)

lemma dgGluingIdentityCommaPrism_component_difference
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (hβ : β (J.min' hJ) = 0) :
    HEq ((toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component J k hJ hk -
        dgGluingIdentityCommaReplacementComponent R E s J k hJ hk)
      (dgGluingCommaPrismCorrectionSum R E E (DGFunctor.id E) s.val.toSimplexData
        (pinchedPrismPhase β) (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (two_withLast hJ) (min_withLast hJ _) (max_withLast J _)
        (by rw [card_withLast]; omega)) := by
  have hx : x = (s.val.obj (J.min' hJ).castSucc).replacement :=
    (congrArg (fun Z : DGFunctorCommaObject R E E (DGFunctor.id E) => Z.replacement)
      (source_obj s (J.min' hJ))).symm
  have hy : y = (s.val.obj (Fin.last (n + 1))).source :=
    (congrArg (fun Z : DGFunctorCommaObject R E E (DGFunctor.id E) => Z.source)
      (target_obj s)).symm
  have hs := gradedHom_sub_heq hx hy rfl _ _ _ _
    (dgGluingIdentityCommaPrism_component_mixed R E s J k hJ hk β hβ)
    (dgGluingIdentityCommaPrism_main_component R E s J k hJ hk).symm
  refine hs.trans (heq_of_eq ?_)
  rw [dgGluingCommaPrismMixedCoefficient_eq, add_sub_cancel_left]

end SerrePositivity.InfinityCategories
