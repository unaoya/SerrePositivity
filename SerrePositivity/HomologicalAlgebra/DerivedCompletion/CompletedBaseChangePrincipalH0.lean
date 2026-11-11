module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraH0
public import SerrePositivity.HomologicalAlgebra.TorBaseChange

/-!
# 主元完備底変換の零次と通常テンソル環の実完備化

## 概要
主元完備導来底変換の H⁰ を、通常テンソル環の実主元完備化と係数線形に比較する。
## 方針
係数拡大の標準 augmentation の零次同型を完備化し、既存の代数 H⁰ 比較を使う。
## 規約
平坦性・有界ねじれを仮定しない。比較は元の標準 augmentation による。
## 使われ方
BS 著者版 Proposition 7.10 の完備な有限関係包絡の忠実平坦性。
-/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B A : Type u) [CommRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra R A]

/-- 主元完備導来底変換の零次は、通常テンソル環の実主元完備化に係数線形に同型。 -/
def completedBaseChangeTensorPrincipalH0LinearEquiv (p : ℕ) :
    let T := B ⊗[R] A
    letI := principalCompletionCommRing T (p : T)
    letI : Algebra B (PrincipalCompletionH0 T (p : T)) :=
      ((principalCompletionUnitRingHom T (p : T)).comp (algebraMap B T)).toAlgebra
    (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
        ((derivedComplexCompletionFunctor B (p : B)).obj
          ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))).obj) ≃ₗ[B]
      PrincipalCompletionH0 T (p : T) := by
  let T := B ⊗[R] A
  letI := principalCompletionCommRing T (p : T)
  letI := principalCompletionAlgebra T (p : T)
  let j := principalCompletionUnitRingHom T (p : T)
  letI : Algebra B (PrincipalCompletionH0 T (p : T)) := (j.comp (algebraMap B T)).toAlgebra
  letI : IsScalarTower B T (PrincipalCompletionH0 T (p : T)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let H := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let S := DerivedCategory.singleFunctor (ModuleCat B) 0
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)
  let Y := ((boundedAboveDerivedBaseChange (algebraMap R B)).obj X).obj
  let Y0 := S.obj (ModuleCat.of B T)
  let f := (boundedAboveDerivedBaseChangeModuleAugmentation (algebraMap R B)).app (ModuleCat.of R A)
  let e := (extendScalarsObjEquivTensor R B (ModuleCat.of R A)).toModuleIso
  let g : Y ⟶ Y0 := f ≫ S.map e.hom
  have hf : IsIso (H.map f) := by
    have h : IsIso (H.map f ≫ (realizedSingleH0Iso B).hom.app
        ((ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R A))) := by
      rw [boundedAboveDerivedBaseChangeModuleAugmentation_homology]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((realizedSingleH0Iso B).hom.app
      ((ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R A)))
  have hg : IsIso (H.map g) := by
    dsimp [g]
    rw [Functor.map_comp]
    infer_instance
  letI : X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)).IsLE 0
    infer_instance
  letI : Y.IsLE 0 := boundedAboveLeftDerived_isLE (ModuleCat.extendScalars (algebraMap R B)) X 0
  letI : Y0.IsLE 0 := by dsimp [Y0]; infer_instance
  have hgc := derivedComplexCompletion_h0_map_isIso B (p : B) g inferInstance inferInstance hg
  let U := completedAlgebra B (p : B) T
  letI := derivedH0CommRing U
  letI := derivedH0Algebra U
  letI := completedAlgebraScalarAlgebra B (p : B) T
  letI := completedAlgebraScalarTower B (p : B) T
  let e1 := ((completedAlgebraH0NatPrincipalAlgEquiv B T p).restrictScalars B).toLinearEquiv
  exact (asIso (H.map ((derivedComplexCompletionFunctor B (p : B)).map g))).toLinearEquiv.trans e1

end SerrePositivity.DerivedCompletion
