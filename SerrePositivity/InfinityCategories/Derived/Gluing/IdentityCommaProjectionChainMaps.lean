module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPinchedProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedSimplexChainMap

/-! 元の二 pinched 射影を同じ Hom 鎖射影へ厳密に照合する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E] (x y : E)

lemma dgGluingIdentityCommaReplacementPinchedMap_chainMap :
    dgGluingIdentityCommaReplacementPinchedMap R E x y =
      pinchedHomChainMap (dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  exact dgGluingFunctorPinchedSimplex_chainMap
    (dgCommaAugmentationSource R E E (DGFunctor.id E)) s

lemma dgGluingIdentityCommaTarget_map :
    (dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) =
      dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) := by
  change dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ 𝟙 _ = _
  exact Category.comp_id _

lemma dgGluingIdentityCommaSourcePinchedMap_chainMap :
    dgGluingIdentityCommaSourcePinchedMap R E x y =
      pinchedHomChainMap (dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) := by
  have h : dgGluingIdentityCommaSourcePinchedMap R E x y =
      pinchedHomChainMap ((dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact dgGluingFunctorPinchedSimplex_chainMap
      (dgCommaAugmentationTarget R E E (DGFunctor.id E)) s
  exact h.trans (congrArg (fun f => pinchedHomChainMap f)
    (dgGluingIdentityCommaTarget_map R E x y))

end SerrePositivity.InfinityCategories
