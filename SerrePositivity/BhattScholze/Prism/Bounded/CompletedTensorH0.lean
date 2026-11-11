module

public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorFlatness
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraH0
import SerrePositivity.HomologicalAlgebra.TorBaseChange

/-!
# 完備導来テンソル積の零次

## 概要
上に有界な完備導来テンソル積の H⁰ は、通常のテンソル積の二座標完備化と係数線形に同型。

## 方針
係数拡大の標準 augmentation と、単一座標完備化の標準 H⁰ 比較を二度使う。

## 規約
BS 著者版 Corollary 3.12 (a)。p と左因子の指定生成元で完備化する。

## 使われ方
完備テンソル積の完全忠実平坦性。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

private theorem isIso_homology_augmentation {R : Type u} [CommRing R]
    (X : DerivedCategory (ModuleCat.{u} R)) [X.IsLE 0] :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map (derivedNonpositiveAugmentation X)) := by
  have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (derivedNonpositiveAugmentation X) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app _) := by
    rw [derivedNonpositiveAugmentation_homology]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app _)

private def h0AugmentationIso (g : A →+* B)
    (h : g = algebraMap A B) (M : ModuleCat.{u} A) :
    let F := DerivedCategory.homologyFunctor (ModuleCat B) 0
    let X := ((boundedAboveDerivedBaseChange g).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    F.obj X ≅ ModuleCat.of B (B ⊗[A] M) := by
  subst g
  let F := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let q := algebraMap A B
  let f := (boundedAboveDerivedBaseChangeModuleAugmentation q).app M
  have hF : IsIso (F.map f) := by
    have : IsIso (F.map f ≫ (realizedSingleH0Iso B).hom.app ((ModuleCat.extendScalars q).obj M)) := by
      rw [boundedAboveDerivedBaseChangeModuleAugmentation_homology]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((realizedSingleH0Iso B).hom.app _)
  exact asIso (F.map f) ≪≫ (realizedSingleH0Iso B).app ((ModuleCat.extendScalars q).obj M) ≪≫
    (extendScalarsObjEquivTensor A B M).toModuleIso

/-- 概要：二座標完備導来底変換の H⁰ と完備テンソル積との線形同値。
方針：導来係数拡大の H⁰ と通常テンソル積を比較してから、二つの主元完備化を順に計算する。
規約：BS 著者版 Corollary 3.12 (a) の完備化。係数は左因子。
使われ方：完備テンソル積の完全平坦性を導来模型から移す。 -/
def pairCompletedBaseChangeH0LinearEquiv {p : ℕ} [Fact p.Prime] (P : OrientedPrism p B) :
    let Y := pairCompletedBaseChange (algebraMap A B) (p : B) P.generator
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A C))
    let H := PrismCompletedTensor (A := A) (C := C) P
    letI := (prismCompletedTensorLeft P (A := A) (C := C)).toAlgebra
    (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj Y.obj ≃ₗ[B] H := by
  let T := B ⊗[A] C
  let d := P.generator
  let H := PrismCompletedTensor (A := A) (C := C) P
  let l : B →+* H := prismCompletedTensorLeft P
  let := l.toAlgebra
  let F := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let S := DerivedCategory.singleFunctor (ModuleCat B) 0
  let F₁ := derivedComplexCompletionFunctor B (p : B)
  let F₂ := derivedComplexCompletionFunctor B d
  let X := (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A C))
  let Y := ((boundedAboveDerivedBaseChange (algebraMap A B)).obj X).obj
  let Y₀ := S.obj (ModuleCat.of B T)
  let : X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A C)).IsLE 0
    infer_instance
  let : Y.IsLE 0 := boundedAboveLeftDerived_isLE (ModuleCat.extendScalars (algebraMap A B))
    X 0
  let f : Y ⟶ Y₀ := derivedNonpositiveAugmentation Y ≫
    S.map (h0AugmentationIso (algebraMap A B) rfl (ModuleCat.of A C)).hom
  have hf : IsIso (F.map f) := by
    let := isIso_homology_augmentation Y
    simp only [f, Functor.map_comp]
    infer_instance
  have hf₁ := derivedComplexCompletion_h0_map_isIso B (p : B) f inferInstance inferInstance hf
  have hf₂ := derivedComplexCompletion_h0_map_isIso B d (F₁.map f)
    (derivedComplexCompletionFunctor_isLE B (p : B) Y 0 inferInstance)
    (derivedComplexCompletionFunctor_isLE B (p : B) Y₀ 0 inferInstance) hf₁
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
  let e₁ : F.obj (F₁.obj Y₀) ≃ₗ[B] T₁ :=
    ((completedAlgebraH0NatPrincipalAlgEquiv B T p).restrictScalars B).toLinearEquiv
  let : (F₁.obj Y₀).IsLE 0 :=
    derivedComplexCompletionFunctor_isLE B (p : B) Y₀ 0 inferInstance
  let g : F₁.obj Y₀ ⟶ S.obj (ModuleCat.of B T₁) :=
    derivedNonpositiveAugmentation (F₁.obj Y₀) ≫ S.map e₁.toModuleIso.hom
  have hg : IsIso (F.map g) := by
    let := isIso_homology_augmentation (F₁.obj Y₀)
    simp only [g, Functor.map_comp]
    infer_instance
  have hg₂ := derivedComplexCompletion_h0_map_isIso B d g inferInstance inferInstance hg
  let d₁ := algebraMap B T₁ d
  let T₂ := PrincipalCompletionH0 T₁ d₁
  let : CommRing T₂ := principalCompletionCommRing T₁ d₁
  let : Algebra T₁ T₂ := principalCompletionAlgebra T₁ d₁
  let u₂ := principalCompletionUnitRingHom T₁ d₁
  let : Algebra B T₂ := (u₂.comp (algebraMap B T₁)).toAlgebra
  let : IsScalarTower B T₁ T₂ := IsScalarTower.of_algebraMap_eq' rfl
  let V := completedAlgebra B d T₁
  let := derivedH0CommRing V
  let := derivedH0Algebra V
  let := completedAlgebraScalarAlgebra B d T₁
  let := completedAlgebraScalarTower B d T₁
  let e₂ : F.obj (F₂.obj (S.obj (ModuleCat.of B T₁))) ≃ₗ[B] T₂ :=
    ((completedAlgebraPrincipalH0AlgEquiv B d T₁).restrictScalars B).toLinearEquiv
  let er : H ≃+* T₂ := pdCompletionIteratedEquiv T p (algebraMap B T d)
  let e₃ : H ≃ₗ[B] T₂ :=
    { er.toAddEquiv with
      map_smul' := by
        intro b x
        change er (l b * x) = algebraMap B T₂ b * er x
        rw [map_mul]
        have he : er (l b) = algebraMap B T₂ b :=
          pdCompletionIteratedEquiv_unit T p (algebraMap B T d) (algebraMap B T b)
        rw [he] }
  exact (asIso (F.map (F₂.map (F₁.map f)))).toLinearEquiv.trans
    ((asIso (F.map (F₂.map g))).toLinearEquiv.trans (e₂.trans e₃.symm))

end SerrePositivity.BhattScholze.Prismatic
