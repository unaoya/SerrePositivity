module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismIntervalCut
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaAugmentationEvaluation
public import SerrePositivity.InfinityCategories.F1.CoherentPrismEvaluation

/-! 元恒等 comma の augmentation 四角形と pinched prism の全区間評価の厳密な等式。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] (x y : E)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "HP" => DGNerve.pinchedHom R Q
  (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)

lemma dgGluingIdentityCommaPrismInterval_square :
    (Δ[1] ◁ intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
      (Simplex.vertex (dgGluingIdentityCommaObject R E x))
      (Simplex.vertex (dgGluingIdentityCommaObject R E y)))) ≫
        dgGluingIdentityCommaAugmentationPrism R E =
      (α_ (Δ[1] : SSet.{max u v}) Δ[1] HP).inv ≫
        ((β_ (Δ[1] : SSet.{max u v}) Δ[1]).hom ▷ HP) ≫
          (α_ (Δ[1] : SSet.{max u v}) Δ[1] HP).hom ≫
            (Δ[1] ◁ dgGluingIdentityCommaPinchedPrism R E x y) ≫
              intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R E)
                (Simplex.vertex x) (Simplex.vertex y)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨β, t, s⟩
  have hq := pinchedHomToIntervalMappingSpace_evaluate (𝟙 HP) s t
  rw [Category.id_comp] at hq
  have he := pinchedHomToIntervalMappingSpace_evaluate
    (𝟙 (DGNerve.pinchedHom R E x y))
    (dgGluingIdentityCommaPinchedPrismSimplex R E s (stdSimplex.objEquiv β).toOrderHom) t
  rw [Category.id_comp] at he
  have hq' : (intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
      (Simplex.vertex (dgGluingIdentityCommaObject R E x))
      (Simplex.vertex (dgGluingIdentityCommaObject R E y)))).app (Opposite.op ⦋n⦌) (t, s) =
      s.val.pullback (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom) := hq
  have he' : (intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R E)
      (Simplex.vertex x) (Simplex.vertex y))).app (Opposite.op ⦋n⦌)
      (t, dgGluingIdentityCommaPinchedPrismSimplex R E s (stdSimplex.objEquiv β).toOrderHom) =
      (dgGluingIdentityCommaPinchedPrismSimplex R E s
        (stdSimplex.objEquiv β).toOrderHom).val.pullback
        (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom) := he
  have hl := congrArg (fun z : Simplex R Q n =>
    (dgGluingIdentityCommaAugmentationPrism R E).app (Opposite.op ⦋n⦌) (β, z)) hq'
  have ha := dgGluingIdentityCommaAugmentationPrism_evaluate R E β
    (s.val.pullback (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom))
  exact hl.trans (ha.trans ((dgGluingIdentityCommaPrismInterval_cut R E s
    (stdSimplex.objEquiv β).toOrderHom (stdSimplex.objEquiv t).toOrderHom).symm.trans he'.symm))

end SerrePositivity.InfinityCategories
