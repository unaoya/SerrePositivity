module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra

/-! # Original coefficient multiplication in the actual derived tensor H⁰ ring -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The original H⁰ algebra comparison respects arbitrary linear maps of the left coefficient. -/
lemma derivedTensorH0AlgEquiv_map_left
    (f : ModuleCat.of R S ⟶ ModuleCat.of R S)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    derivedTensorH0AlgEquiv S T
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map f)
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))))).hom x) =
      (((tensoringLeft (ModuleCat R)).map f).app (ModuleCat.of R T)).hom
        (derivedTensorH0AlgEquiv S T x) := by
  let M := ModuleCat.of R S
  let N := ModuleCat.of R T
  let A := (boundedAboveDerivedTensorModuleAugmentation M).app N
  let t := boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
    (boundedAboveDerivedSingleFunctor.map f) (𝟙 (boundedAboveDerivedSingleFunctor.obj N)))
  let k := ((tensoringLeft (ModuleCat R)).map f).app N
  have hn := congrArg (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    (boundedAboveDerivedTensorModuleAugmentation_naturality_left f N)
  simp only [Functor.map_comp] at hn
  have hx : (DerivedCategory.homologyFunctor (ModuleCat R) 0).map A
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map t.hom x) =
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).map k)
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map A x) :=
    congrArg (fun h => h.hom x) hn
  simp only [derivedTensorH0AlgEquiv_apply, derivedTensorH0AlgHom_apply]
  rw [hx]
  exact derivedSingleH0_map_apply k _

/-- Multiplication in the original left coefficient is multiplication by its original H⁰ factor image. -/
lemma derivedTensorH0_left_coefficient_mul (s : S)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R s)))
        (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))))).hom x =
      derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R S) s) * x := by
  letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
  letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) S T)
  let f : ModuleCat.of R S ⟶ ModuleCat.of R S := ModuleCat.ofHom (LinearMap.mulLeft R s)
  have hk (z : S ⊗[R] T) :
      (((tensoringLeft (ModuleCat R)).map f).app (ModuleCat.of R T)).hom z =
        (s ⊗ₜ[R] (1 : T)) * z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change (s * a) ⊗ₜ[R] b = (s ⊗ₜ[R] (1 : T)) * (a ⊗ₜ[R] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have hs : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
      (ModuleCat.of R S)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R S) s) = s :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
      (ModuleCat.of R S)).toLinearEquiv.apply_symm_apply s
  let c : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R S) s
  have hfac : derivedTensorH0AlgEquiv S T
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c) =
      s ⊗ₜ[R] (1 : T) := by
    change derivedTensorH0AlgHom S T
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c) = _
    rw [derivedTensorH0AlgHom_left]
    change (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R S) ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat R) 0).inv.app (ModuleCat.of R S) s)) = _
    rw [hs]
    rfl
  apply (derivedTensorH0AlgEquiv S T).injective
  rw [derivedTensorH0AlgEquiv_map_left, hk, map_mul]
  change (s ⊗ₜ[R] (1 : T)) * derivedTensorH0AlgEquiv S T x =
    derivedTensorH0AlgEquiv S T
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c) *
        derivedTensorH0AlgEquiv S T x
  rw [hfac]

end SerrePositivity
