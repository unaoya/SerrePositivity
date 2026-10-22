module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPinchedPrismFamily
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPinchedProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismZero
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyOfPrism

/-! 同じ実 augmentation prism は、二つの実 pinched Hom 射影の間の全ホモトピーを与える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] (x y : E)

lemma dgGluingIdentityCommaPinchedPrism_zero :
    prismEndpoint 0 _ ≫ dgGluingIdentityCommaPinchedPrism R E x y =
      dgGluingIdentityCommaReplacementPinchedMap R E x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply InfinityCategories.PinchedHom.Simplex.ext
  change dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s.val
    (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) =
      (dgGluingFunctorPinchedSimplex.{u, max u v, v, 0}
        (dgCommaAugmentationSource R E E (DGFunctor.id E)) s).val
  rw [dgGluingFunctorPinchedSimplex_val]
  exact dgGluingIdentityCommaPrism_zero R E s.val y (target_obj s)

lemma dgGluingIdentityCommaPinchedPrism_one :
    prismEndpoint 1 _ ≫ dgGluingIdentityCommaPinchedPrism R E x y =
      dgGluingIdentityCommaSourcePinchedMap R E x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply InfinityCategories.PinchedHom.Simplex.ext
  exact (dgGluingIdentityCommaPinchedPrism_one_val R E s).trans
    (dgGluingFunctorPinchedSimplex_val.{u, max u v, v, 0}
      (dgCommaAugmentationTarget R E E (DGFunctor.id E)) s).symm

def dgGluingIdentityCommaPinchedHomotopy :
    SSet.Homotopy (dgGluingIdentityCommaReplacementPinchedMap R E x y)
      (dgGluingIdentityCommaSourcePinchedMap R E x y) :=
  dgGluingHomotopyOfPrism (dgGluingIdentityCommaPinchedPrism R E x y)
    (dgGluingIdentityCommaPinchedPrism_zero R E x y)
    (dgGluingIdentityCommaPinchedPrism_one R E x y)

end SerrePositivity.InfinityCategories
