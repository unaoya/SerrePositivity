module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaObject
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedSimplexNaturality

/-! 恒等 augmentation の実 pinched Hom の二射影を、元の全 dg 関手像で実現する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

def dgGluingIdentityCommaReplacementPinchedMap (x y : E) :
    DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
      (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ⟶
      DGNerve.pinchedHom R E x y where
  app d := ↾fun s => dgGluingFunctorPinchedSimplex.{u, max u v, v, 0}
    (dgCommaAugmentationSource R E E (DGFunctor.id E)) s
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    exact (dgGluingFunctorPinchedSimplex_pullback.{u, max u v, v, 0}
      (dgCommaAugmentationSource R E E (DGFunctor.id E)) s α.unop).symm

def dgGluingIdentityCommaSourcePinchedMap (x y : E) :
    DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
      (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ⟶
      DGNerve.pinchedHom R E x y where
  app d := ↾fun s => dgGluingFunctorPinchedSimplex.{u, max u v, v, 0}
    (dgCommaAugmentationTarget R E E (DGFunctor.id E)) s
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    exact (dgGluingFunctorPinchedSimplex_pullback.{u, max u v, v, 0}
      (dgCommaAugmentationTarget R E E (DGFunctor.id E)) s α.unop).symm

end SerrePositivity.InfinityCategories
