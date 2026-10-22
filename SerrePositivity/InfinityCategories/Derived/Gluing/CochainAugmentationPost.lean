module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismChainComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaPostData
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedInputChainMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainAugmentationHomotopy

/-! 同じ実 augmentation による全 cochain prism は、任意の Hom 鎖写像の後合成に自然。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (E T : Type (max u v))
  [DGCategory R E] [DGCategory R T] (x y : E) (x' y' : T)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (q : homObject R E x y ⟶ homObject R T x' y')
local notation "F" => dgGluingCochainIdentityCommaLift R E x y K f g h he
local notation "G" => dgGluingCochainIdentityCommaLift R T x' y' K (f ≫ q) (g ≫ q)
  (h.comp (Cochain.ofHom q) (add_zero (-1))) (dgGluingCochainPost_boundary f g h he q)

lemma dgGluingCochainAugmentationPrism_post :
    dgGluingCochainAugmentationPrism R E x y K f g h he ≫ pinchedHomChainMap q =
      dgGluingCochainAugmentationPrism R T x' y' K (f ≫ q) (g ≫ q)
        (h.comp (Cochain.ofHom q) (add_zero (-1))) (dgGluingCochainPost_boundary f g h he q) := by
  have hiE := dgGluingComplexPinchedInput_eq_chainMap
    (E := DGFunctorCommaObject R E E (DGFunctor.id E))
    (x := dgGluingIdentityCommaObject R E x) (y := dgGluingIdentityCommaObject R E y) F
  have hiT := dgGluingComplexPinchedInput_eq_chainMap
    (E := DGFunctorCommaObject R T T (DGFunctor.id T))
    (x := dgGluingIdentityCommaObject R T x') (y := dgGluingIdentityCommaObject R T y') G
  have ht := dgGluingIdentityCommaPrism_chain_input_compare R
    (DGComplexPinchedModel.{u, max u v} K) E T (complexPinchedSource K) (complexPinchedTarget K)
    x y x' y' ((complexUnitHomIso K).inv ≫ F) ((complexUnitHomIso K).inv ≫ G) q
    (dgGluingCochainIdentityCommaPost_source R E T x y x' y' K f g h he q _)
    (dgGluingCochainIdentityCommaPost_replacement R E T x y x' y' K f g h he q _)
    (dgGluingCochainIdentityCommaPost_pre_primitive R E T x y x' y' K f g h he q _)
  simp only [dgGluingCochainAugmentationPrism, dgGluingCochainIdentityCommaPinchedInput,
    hiE, hiT, Category.assoc]
  exact ht

end SerrePositivity.InfinityCategories
