module
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedNonpositiveHom
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive

/-! # Original maps from a derived tensor to a pure algebra factor through ordinary tensor H⁰ -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0]
local notation "B" => boundedAboveDerivedTensorAlgebra (R := R) S T
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj

/-- The standard augmentation realizes the actual H⁰ algebra map to any given pure target. -/
lemma derivedTensorAlgebraMap_factor_pure (f : B ⟶ A) :
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (B).X.obj ≃ₐ[R] S ⊗[R] T :=
      derivedTensorH0AlgEquiv (R := R) S T
    let g : S ⊗[R] T →ₐ[R] H := (derivedH0AlgMap f).comp e.symm.toAlgHom
    f.hom.hom = (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom ≫
      boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom g.toLinearMap) ≫
      (pureDerivedAlgebraSingleIso R A).inv := by
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (B).X.obj ≃ₐ[R] S ⊗[R] T :=
    derivedTensorH0AlgEquiv (R := R) S T
  let g : S ⊗[R] T →ₐ[R] H := (derivedH0AlgMap f).comp e.symm.toAlgHom
  let f0 : (B).X.obj ⟶ A.X.obj := f.hom.hom.hom
  let ε : (B).X.obj ⟶
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R (S ⊗[R] T)) :=
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom
  let hle : (B).X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R S)).obj
      (ModuleCat.of R T)).IsLE 0
    infer_instance
  apply (cancel_mono (pureDerivedAlgebraSingleIso R A).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply InducedCategory.hom_ext
  change f0 ≫ (normalizedPureHomologyIso A.X.obj 0).hom =
    ε ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map (ModuleCat.ofHom g.toLinearMap)
  apply (derivedNonpositiveHomologyZero_map_bijective
    (X := (B).X.obj) (Y := (DerivedCategory.singleFunctor (ModuleCat R) 0).obj H)).injective
  let σ := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0
  apply (cancel_mono (σ.hom.app H)).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [normalizedPureHomologyIso_homology]
  have hn := σ.hom.naturality (ModuleCat.ofHom g.toLinearMap)
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).map (ModuleCat.ofHom g.toLinearMap)) ≫
      σ.hom.app H = σ.hom.app (ModuleCat.of R (S ⊗[R] T)) ≫
      ModuleCat.ofHom g.toLinearMap at hn
  rw [hn, Category.comp_id]
  ext x
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map f0 x =
    g ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
      (ModuleCat.of R (S ⊗[R] T))
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ε x))
  have hε : ε = (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app
      (ModuleCat.of R T) := boundedAboveDerivedTensorAlgebraAugmentation_hom S T
  have hv :
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
          (ModuleCat.of R (S ⊗[R] T))
          ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map ε x) = e x := by
    have hx := congrArg (fun k => (DerivedCategory.homologyFunctor (ModuleCat R) 0).map k x) hε
    exact (congrArg
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R (S ⊗[R] T))) hx).trans
      (derivedTensorH0AlgHom_apply (R := R) S T x).symm
  calc
    _ = derivedH0AlgMap f x := (derivedH0AlgMap_apply f x).symm
    _ = g (e x) := by
      simp only [g, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply]
    _ = _ := congrArg g hv.symm

end SerrePositivity
