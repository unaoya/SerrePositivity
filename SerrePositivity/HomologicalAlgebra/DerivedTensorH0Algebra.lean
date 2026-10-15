module
public import SerrePositivity.HomologicalAlgebra.DerivedSingleH0Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAlgebraAugmentation
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # The actual H⁰ algebra of the derived tensor and the ordinary tensor algebra -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The standard augmentation is always an isomorphism in degree zero. -/
lemma derivedTensorAugmentation_h0_isIso (M N : ModuleCat.{u} R) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((boundedAboveDerivedTensorModuleAugmentation M).app N)) := by
  let h := (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((boundedAboveDerivedTensorModuleAugmentation M).app N)
  have : IsIso (h ≫ (realizedSingleH0Iso R).hom.app ((tensorLeft M).obj N)) := by
    dsimp only [h]
    rw [boundedAboveDerivedTensorModuleAugmentation_homology]
    infer_instance
  exact IsIso.of_isIso_comp_right h ((realizedSingleH0Iso R).hom.app ((tensorLeft M).obj N))

/-- The actual H⁰ augmentation, followed by the canonical discrete comparison, is an algebra map. -/
def derivedTensorH0AlgHom (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) S T)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj →ₐ[R] S ⊗[R] T := by
  letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
  letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) S T)
  letI : CommRing
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R (S ⊗[R] T))) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T))
  letI : Algebra R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R (S ⊗[R] T))) :=
    derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T))
  exact (derivedSingleH0AlgEquiv (R := R) (S ⊗[R] T)).toAlgHom.comp
    (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T))

/-- Its function uses exactly the original augmentation and the canonical single H⁰ comparison. -/
lemma derivedTensorH0AlgHom_apply (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    derivedTensorH0AlgHom S T x =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R (S ⊗[R] T))
        ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
          ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app
            (ModuleCat.of R T)) x) := by
  change (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
    (ModuleCat.of R (S ⊗[R] T))
    (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x) = _
  rw [derivedH0AlgMap_apply, boundedAboveDerivedTensorAlgebraAugmentation_hom]
  rfl

/-- No Tor vanishing or flatness is needed for the H⁰ algebra comparison to be bijective. -/
lemma derivedTensorH0AlgHom_bijective (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : Function.Bijective (derivedTensorH0AlgHom (R := R) S T) := by
  let := derivedTensorAugmentation_h0_isIso (ModuleCat.of R S) (ModuleCat.of R T)
  have h := ConcreteCategory.bijective_of_isIso
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app (ModuleCat.of R T)))
  have he := ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
    (ModuleCat.of R (S ⊗[R] T))).toLinearEquiv.bijective
  have hb : Function.Bijective (fun x :
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj ↦
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R (S ⊗[R] T))
        ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
          ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app
            (ModuleCat.of R T)) x)) := he.comp h
  simpa only [← derivedTensorH0AlgHom_apply] using hb

/-- The actual H⁰ of the derived tensor is the ordinary tensor as an R-algebra. -/
def derivedTensorH0AlgEquiv (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) S T)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj ≃ₐ[R] S ⊗[R] T := by
  letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
  letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) S T)
  exact AlgEquiv.ofBijective (derivedTensorH0AlgHom (R := R) S T)
    (derivedTensorH0AlgHom_bijective S T)

/-- The comparison function is exactly the standard augmentation followed by canonical H⁰. -/
lemma derivedTensorH0AlgEquiv_apply (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    derivedTensorH0AlgEquiv S T x = derivedTensorH0AlgHom S T x := rfl

/-- The canonical single comparison is natural for arbitrary linear coefficient maps. -/
lemma derivedSingleH0_map_apply {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app N
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).map f) x) =
    f.hom ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app M x) := by
  exact congrArg (fun k ↦ k.hom x)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.naturality f)

/-- The left factor has exactly the ordinary tensor inclusion under the H⁰ algebra comparison. -/
lemma derivedTensorH0AlgHom_left (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) :
    derivedTensorH0AlgHom S T
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) x) =
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R S) x) := by
  rw [derivedTensorH0AlgHom_apply, derivedH0AlgMap_apply]
  have h := congrArg (fun k ↦ (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    k.hom.hom.hom x) (boundedAboveDerivedTensorAlgebraLeft_augmentation (R := R) S T)
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((boundedAboveDerivedTensorAlgebraLeft (R := R) S T).hom.hom.hom ≫
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom) x = _ at h
  rw [CategoryTheory.Functor.map_comp, boundedAboveDerivedTensorAlgebraAugmentation_hom] at h
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app (ModuleCat.of R T))
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (boundedAboveDerivedTensorAlgebraLeft (R := R) S T).hom.hom.hom x) = _ at h
  rw [h]
  exact derivedSingleH0_map_apply
    (ModuleCat.ofHom (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toLinearMap) x

/-- The right factor has exactly the ordinary tensor inclusion under the H⁰ algebra comparison. -/
lemma derivedTensorH0AlgHom_right (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj) :
    derivedTensorH0AlgHom S T
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraRight (R := R) S T) x) =
    (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R T) x) := by
  rw [derivedTensorH0AlgHom_apply, derivedH0AlgMap_apply]
  have h := congrArg (fun k ↦ (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    k.hom.hom.hom x) (boundedAboveDerivedTensorAlgebraRight_augmentation (R := R) S T)
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((boundedAboveDerivedTensorAlgebraRight (R := R) S T).hom.hom.hom ≫
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom) x = _ at h
  rw [CategoryTheory.Functor.map_comp, boundedAboveDerivedTensorAlgebraAugmentation_hom] at h
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app (ModuleCat.of R T))
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (boundedAboveDerivedTensorAlgebraRight (R := R) S T).hom.hom.hom x) = _ at h
  rw [h]
  exact derivedSingleH0_map_apply
    (ModuleCat.ofHom (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toLinearMap) x

end SerrePositivity
