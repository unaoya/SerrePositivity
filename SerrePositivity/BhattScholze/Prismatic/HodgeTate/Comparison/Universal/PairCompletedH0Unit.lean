module

public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorH0
public import SerrePositivity.HomologicalAlgebra.TorBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.IteratedCompletionH0Unit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.PrincipalCompletionCoefficientUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CompletedAlgebraCoefficientUnitHomology
import all SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorH0

/-!
# 元の二座標完備テンソル積のH⁰同型と単位

## 概要
元のH⁰線形同型は、通常テンソル積への元の増大を二座標完備化の単位へ送る。

## 方針
二回の単位の自然性、非正次数増大の正規化、既存の係数代数同値を使う。

## 規約
既存のpairCompletedBaseChangeH0LinearEquivの法則を証明し、同型を選び直さない。

## 使われ方
元のfull envelopeの指定同型を元の係数射と照合する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

/-- 元のH⁰同型は元の二回完備化単位で正規化される。 -/
theorem pairCompletedBaseChangeH0LinearEquiv_unit {p : ℕ} [Fact p.Prime]
    (P : OrientedPrism p B) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
    let Y := ((boundedAboveDerivedBaseChange (algebraMap A B)).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A C))).obj
    ∀ x : H.obj Y,
      pairCompletedBaseChangeH0LinearEquiv (A := A) (C := C) P
        (H.map ((derivedComplexCompletionUnit B (p : B)).app Y ≫
          (derivedComplexCompletionUnit B P.generator).app
            ((derivedComplexCompletionFunctor B (p : B)).obj Y)) x) =
      pdCompletionUnit (B ⊗[A] C) p
        (algebraMap B (B ⊗[A] C) P.generator)
        (((H.map ((boundedAboveDerivedBaseChangeModuleAugmentation (algebraMap A B)).app
          (ModuleCat.of A C)) ≫
          (realizedSingleH0Iso B).hom.app
            ((ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A C))) ≫
          (extendScalarsObjEquivTensor A B (ModuleCat.of A C)).toModuleIso.hom) x) := by
  let T := B ⊗[A] C
  letI := pdCompletionCommRing T p (algebraMap B T P.generator)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} B) 0
  let F₁ := derivedComplexCompletionFunctor B (p : B)
  let F₂ := derivedComplexCompletionFunctor B P.generator
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A C)
  let Y := ((boundedAboveDerivedBaseChange (algebraMap A B)).obj X).obj
  let Y₀ := S.obj (ModuleCat.of B T)
  let : X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A C)).IsLE 0
    infer_instance
  let : Y.IsLE 0 := boundedAboveLeftDerived_isLE (ModuleCat.extendScalars (algebraMap A B)) X 0
  let e₀ : H.obj Y ⟶ ModuleCat.of B T :=
    H.map ((boundedAboveDerivedBaseChangeModuleAugmentation (algebraMap A B)).app
      (ModuleCat.of A C)) ≫
      (realizedSingleH0Iso B).hom.app
        ((ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A C)) ≫
      (extendScalarsObjEquivTensor A B (ModuleCat.of A C)).toModuleIso.hom
  let f : Y ⟶ Y₀ := derivedNonpositiveAugmentation Y ≫ S.map e₀
  let T₁ := PrincipalCompletionH0 T (p : T)
  let : CommRing T₁ := principalCompletionCommRing T (p : T)
  let : Algebra T T₁ := principalCompletionAlgebra T (p : T)
  let u₁ := principalCompletionUnitRingHom T (p : T)
  let : Algebra B T₁ := (u₁.comp (algebraMap B T)).toAlgebra
  let : IsScalarTower B T T₁ := IsScalarTower.of_algebraMap_eq' rfl
  let U := completedAlgebra B (p : B) T
  let := derivedH0CommRing U
  let := derivedH0Algebra U
  let := completedAlgebraScalarAlgebra B (p : B) T
  let := completedAlgebraScalarTower B (p : B) T
  let e₁ : H.obj (F₁.obj Y₀) ≃ₗ[B] T₁ :=
    ((completedAlgebraH0NatPrincipalAlgEquiv B T p).restrictScalars B).toLinearEquiv
  let : (F₁.obj Y₀).IsLE 0 :=
    derivedComplexCompletionFunctor_isLE B (p : B) Y₀ 0 inferInstance
  let g : F₁.obj Y₀ ⟶ S.obj (ModuleCat.of B T₁) :=
    derivedNonpositiveAugmentation (F₁.obj Y₀) ≫ S.map e₁.toModuleIso.hom
  let d₁ := algebraMap B T₁ P.generator
  let T₂ := PrincipalCompletionH0 T₁ d₁
  let : CommRing T₂ := principalCompletionCommRing T₁ d₁
  let : Algebra T₁ T₂ := principalCompletionAlgebra T₁ d₁
  let u₂ := principalCompletionUnitRingHom T₁ d₁
  let : Algebra B T₂ := (u₂.comp (algebraMap B T₁)).toAlgebra
  let : IsScalarTower B T₁ T₂ := IsScalarTower.of_algebraMap_eq' rfl
  let V := completedAlgebra B P.generator T₁
  let := derivedH0CommRing V
  let := derivedH0Algebra V
  let := completedAlgebraScalarAlgebra B P.generator T₁
  let := completedAlgebraScalarTower B P.generator T₁
  let e₂ : H.obj (F₂.obj (S.obj (ModuleCat.of B T₁))) ≃ₗ[B] T₂ :=
    ((completedAlgebraPrincipalH0AlgEquiv B P.generator T₁).restrictScalars B).toLinearEquiv
  let er := pdCompletionIteratedEquiv T p (algebraMap B T P.generator)
  dsimp only
  intro x
  have hf := nonpositiveAugmentation_postcomp_homology Y (ModuleCat.of B T) e₀
  have hg := nonpositiveAugmentation_postcomp_homology (F₁.obj Y₀)
    (ModuleCat.of B T₁) e₁.toModuleIso.hom
  have ht := iteratedCompletionH0_unit (p : B) P.generator Y
    (ModuleCat.of B T) (ModuleCat.of B T₁) (ModuleCat.of B T₂) f g e₂.toModuleIso.hom
  have hf' : H.map f = e₀ ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).inv.app
        (ModuleCat.of B T) := by
    apply (cancel_mono
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).hom.app
        (ModuleCat.of B T))).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id, H, f, Y₀] using hf
  have hg' : H.map g = e₁.toModuleIso.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).inv.app
        (ModuleCat.of B T₁) := by
    apply (cancel_mono
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).hom.app
        (ModuleCat.of B T₁))).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id, H, g] using hg
  change er.symm (e₂ (H.map (F₂.map g)
    (H.map (F₂.map (F₁.map f)) (H.map ((derivedComplexCompletionUnit B (p : B)).app Y ≫
      (derivedComplexCompletionUnit B P.generator).app (F₁.obj Y)) x)))) = _
  apply er.injective
  rw [RingEquiv.apply_symm_apply, pdCompletionIteratedEquiv_unit]
  have htx := congrArg (fun q => q x) ht
  simp only [ModuleCat.comp_apply] at htx
  change e₂ (H.map (F₂.map g) (H.map (F₂.map (F₁.map f))
    (H.map ((derivedComplexCompletionUnit B (p : B)).app Y ≫
      (derivedComplexCompletionUnit B P.generator).app (F₁.obj Y)) x))) = _ at htx
  rw [htx]
  dsimp only [H] at hf' hg'
  rw [hf', hg']
  simp only [ModuleCat.comp_apply]
  let η := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0
  change e₂ (H.map ((derivedComplexCompletionUnit B P.generator).app (S.obj (ModuleCat.of B T₁)))
    (η.inv.app (ModuleCat.of B T₁) (e₁
      (H.map ((derivedComplexCompletionUnit B (p : B)).app Y₀)
        (η.inv.app (ModuleCat.of B T) (e₀ x)))))) = _
  have h₁ : H.map ((derivedComplexCompletionUnit B (p : B)).app Y₀)
      (η.inv.app (ModuleCat.of B T) (e₀ x)) = completedAlgebraUnitAlgHom B (p : B) T (e₀ x) :=
    (completedAlgebraUnitAlgHom_homology B T (p : B) (e₀ x)).symm
  rw [h₁]
  have h₂ : H.map ((derivedComplexCompletionUnit B P.generator).app (S.obj (ModuleCat.of B T₁)))
      (η.inv.app (ModuleCat.of B T₁) (e₁ (completedAlgebraUnitAlgHom B (p : B) T (e₀ x)))) =
      completedAlgebraUnitAlgHom B P.generator T₁ (e₁ (completedAlgebraUnitAlgHom B (p : B) T (e₀ x))) :=
    (completedAlgebraUnitAlgHom_homology B T₁ P.generator
      (e₁ (completedAlgebraUnitAlgHom B (p : B) T (e₀ x)))).symm
  rw [h₂]
  change completedAlgebraPrincipalH0AlgEquiv B P.generator T₁
    ((completedAlgebraUnitAlgHom B P.generator T₁)
      (completedAlgebraH0NatPrincipalAlgEquiv B T p
        ((completedAlgebraUnitAlgHom B (p : B) T) (e₀ x)))) = _
  rw [principalCompletionCoefficientUnit, completedAlgebraH0NatPrincipalAlgEquiv_unit]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
