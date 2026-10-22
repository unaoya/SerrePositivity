module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainAugmentationModelInput
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismLinearDifference
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedChainMapComponent

/-! 元 dg Hom 上で、実 cochain 入力の二射影と負 primitive の全線形成分を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex HomologicalComplex
open DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [DGCategory R C] [DGCategory R E]
  {a b : C} (x y : E) (f g : homObject R C a b ⟶ homObject R E x y)
  (h : Cochain (homObject R C a b) (homObject R E x y) (-1))
  (he : δ (-1) 0 h = Cochain.ofHom (g - f)) {n : ℕ}
  (s : (DGNerve.pinchedHom R C a b) _⦋n⦌)
local notation "F" => dgGluingCochainIdentityCommaLift R E x y (homObject R C a b) f g h he
local notation "t" => pinchedHomChainMapSimplex F s

lemma dgGluingCochainIdentityCommaInput_source
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    dgGluingIdentityCommaSourceComponent R E t J k hJ hk =
      g.f k ((toLinearData s).component J k hJ hk) := by
  dsimp only [dgGluingIdentityCommaSourceComponent]
  rw [dgGluingPinchedChainMapSimplex_component]
  have hi : F ≫ (dgCommaAugmentationTarget R E E (DGFunctor.id E)).map _ _ = g := by
    rw [dgGluingIdentityCommaTarget_map, dgGluingCochainIdentityCommaLift_end]
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hi k)
    ((toLinearData s).component J k hJ hk)

lemma dgGluingCochainIdentityCommaInput_replacement
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    dgGluingIdentityCommaReplacementComponent R E t J k hJ hk =
      f.f k ((toLinearData s).component J k hJ hk) := by
  dsimp only [dgGluingIdentityCommaReplacementComponent]
  rw [dgGluingPinchedChainMapSimplex_component]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (dgGluingCochainIdentityCommaLift_start
      R E x y (homObject R C a b) f g h he) k) ((toLinearData s).component J k hJ hk)

lemma dgGluingCochainIdentityCommaInput_primitive
    (J : Finset (Fin (n + 1))) (p : ℤ) (hJ : J.Nonempty) (hp : p = 1 - (J.card : ℤ)) :
    dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) p
        ((toLinearData t).component J p hJ hp) =
      -h.v p (p - 1) (by omega) ((toLinearData s).component J p hJ hp) := by
  dsimp only [dgCommaAugmentationHomotopyComponent]
  rw [dgGluingPinchedChainMapSimplex_component]
  have hz := ConcreteCategory.congr_hom
    (Cochain.congr_v (dgGluingCochainIdentityCommaLift_primitive
      R E x y (homObject R C a b) f g h he) p (p - 1) (by omega))
    ((toLinearData s).component J p hJ hp)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.neg_v,
    ModuleCat.hom_neg, LinearMap.neg_apply, ModuleCat.comp_apply] at hz
  convert hz using 1

end SerrePositivity.InfinityCategories
