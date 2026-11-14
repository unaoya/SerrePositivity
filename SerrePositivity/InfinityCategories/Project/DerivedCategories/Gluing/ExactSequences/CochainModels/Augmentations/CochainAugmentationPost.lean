module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.IdentityCommaPrismChainComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CochainIdentityCommaPostData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.ComplexPinchedInputChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.CochainAugmentationHomotopy

/-! 同じ実 augmentation による全 cochain prism は、任意の Hom 鎖写像の後合成に自然。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E T : Type (max u v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R T] (x y : E) (x' y' : T)
  (K : _root_.SerrePositivity.DifferentialGraded.Complex R) (f g : K ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x y)
  (h : Cochain K (_root_.SerrePositivity.DifferentialGraded.homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (q : _root_.SerrePositivity.DifferentialGraded.homObject R E x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R T x' y')
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y K f g h he
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R T x' y' K (f ≫ q) (g ≫ q)
  (h.comp (Cochain.ofHom q) (add_zero (-1))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPost_boundary f g h he q)

lemma dgGluingCochainAugmentationPrism_post :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism R E x y K f g h he ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism R T x' y' K (f ≫ q) (g ≫ q)
        (h.comp (Cochain.ofHom q) (add_zero (-1))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPost_boundary f g h he q) := by
  have hiE := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedInput_eq_chainMap
    (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) F
  have hiT := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedInput_eq_chainMap
    (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R T T (DGFunctor.id T))
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T x') (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T y') G
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_chain_input_compare R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} K) E T (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget K)
    x y x' y' ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ F) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ G) q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPost_source R E T x y x' y' K f g h he q _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPost_replacement R E T x y x' y' K f g h he q _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPost_pre_primitive R E T x y x' y' K f g h he q _)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput,
    hiE, hiT, Category.assoc]
  exact ht

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
