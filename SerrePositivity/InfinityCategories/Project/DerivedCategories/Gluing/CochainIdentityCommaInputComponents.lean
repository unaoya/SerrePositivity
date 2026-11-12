module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainAugmentationModelInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaPrismLinearDifference
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedChainMapComponent

/-! 元 dg Hom 上で、実 cochain 入力の二射影と負 primitive の全線形成分を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex HomologicalComplex

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  {a b : C} (x y : E) (f g : _root_.SerrePositivity.DifferentialGraded.homObject R C a b ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x y)
  (h : Cochain (_root_.SerrePositivity.DifferentialGraded.homObject R C a b) (_root_.SerrePositivity.DifferentialGraded.homObject R E x y) (-1))
  (he : δ (-1) 0 h = Cochain.ofHom (g - f)) {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C a b) _⦋n⦌)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y (homObject R C a b) f g h he
local notation "t" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex F s

lemma dgGluingCochainIdentityCommaInput_source
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaSourceComponent R E t J k hJ hk =
      g.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaSourceComponent]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedChainMapSimplex_component]
  have hi : F ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)).map _ _ = g := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaTarget_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_end]
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hi k)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)

lemma dgGluingCochainIdentityCommaInput_replacement
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementComponent R E t J k hJ hk =
      f.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementComponent]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedChainMapSimplex_component]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_start
      R E x y (homObject R C a b) f g h he) k) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)

lemma dgGluingCochainIdentityCommaInput_primitive
    (J : Finset (Fin (n + 1))) (p : ℤ) (hJ : J.Nonempty) (hp : p = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) p
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData t).component J p hJ hp) =
      -h.v p (p - 1) (by omega) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J p hJ hp) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedChainMapSimplex_component]
  have hz := ConcreteCategory.congr_hom
    (Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_primitive
      R E x y (_root_.SerrePositivity.DifferentialGraded.homObject R C a b) f g h he) p (p - 1) (by omega))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J p hJ hp)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.neg_v,
    ModuleCat.hom_neg, LinearMap.neg_apply, ModuleCat.comp_apply] at hz
  convert hz using 1

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
