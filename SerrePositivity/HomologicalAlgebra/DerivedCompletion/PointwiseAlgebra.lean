module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraH0
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraH0
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 代数の各項 H⁰ 完備化と主完備環の比較

## 概要
各項の H⁰ 完備化関手を、既存の主完備環の係数加群と同定する。

## 方針
既存の代数の H⁰ 比較を元の係数環へ制限し、標準の完備化単位上で照合する。

## 規約
平坦性・正則性・有限性は仮定しない。基底環の加群構造を保つ。

## 使われ方
BS 著者版 Theorem 6.4 の各項の完備係数拡大と実際の環の模型の照合。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.DerivedCompletion

attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (p : ℕ)
variable (A : Type u) [CommRing A] [Algebra R A]

/-- 代数の H⁰ 完備化関手の値と、既存の主完備環の係数加群との標準同型。 -/
def moduleCompletionH0RingIso :
    (moduleCompletionH0Functor R (p : R)).obj (ModuleCat.of R A) ≅
      ModuleCat.of R (CompletedRing p A) := by
  let := derivedH0CommRing (completedAlgebra R (p : R) A)
  let := derivedH0Algebra (completedAlgebra R (p : R) A)
  let := completedAlgebraScalarAlgebra R (p : R) A
  let := completedAlgebraScalarTower R (p : R) A
  let : CommRing (PrincipalCompletionH0 A (p : A)) := principalCompletionCommRing A (p : A)
  let : Algebra A (PrincipalCompletionH0 A (p : A)) := principalCompletionAlgebra A (p : A)
  let : Algebra R (PrincipalCompletionH0 A (p : A)) :=
    ((principalCompletionUnitRingHom A (p : A)).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A (PrincipalCompletionH0 A (p : A)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact ((completedAlgebraH0NatPrincipalAlgEquiv R A p).restrictScalars R).toLinearEquiv.toModuleIso

/-- H⁰ の比較は、実際の完備化単位上で元を保つ。 -/
theorem moduleCompletionH0RingIso_unit (x : A) :
    (moduleCompletionH0RingIso R p A).hom
        (((moduleCompletionH0Unit R (p : R)).app (ModuleCat.of R A)) x) =
      principalCompletionRingCatUnit p (CommRingCat.of A) x := by
  have h := completedAlgebraH0NatPrincipalAlgEquiv_unit R A p x
  rw [completedAlgebraUnitAlgHom_apply, completionH0AlgebraUnit_apply] at h
  exact h

private theorem moduleCompletionH0RingIso_inv_unit (x : A) :
    (moduleCompletionH0RingIso R p A).inv
        (principalCompletionRingCatUnit p (CommRingCat.of A) x) =
      ((moduleCompletionH0Unit R (p : R)).app (ModuleCat.of R A)) x := by
  have h := ConcreteCategory.congr_hom (moduleCompletionH0RingIso R p A).hom_inv_id
    (((moduleCompletionH0Unit R (p : R)).app (ModuleCat.of R A)) x)
  change (moduleCompletionH0RingIso R p A).inv
    ((moduleCompletionH0RingIso R p A).hom
      (((moduleCompletionH0Unit R (p : R)).app (ModuleCat.of R A)) x)) = _ at h
  rw [moduleCompletionH0RingIso_unit] at h
  exact h

variable {A} {B : Type u} [CommRing B] [Algebra R B]

/-- 主完備環との比較は、係数線形な任意の写像について厳密に自然。 -/
theorem moduleCompletionH0RingIso_naturality (f : A →ₗ[R] B) :
    (moduleCompletionH0Functor R (p : R)).map (ModuleCat.ofHom f) ≫
        (moduleCompletionH0RingIso R p B).hom =
      (moduleCompletionH0RingIso R p A).hom ≫
        ModuleCat.ofHom (principalCompletionLinearMap R p f) := by
  apply (cancel_epi (moduleCompletionH0RingIso R p A).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply principalCompletionLinearMap_ext R p (completedRing_isModuleComplete R p (A := B))
  intro x
  change (moduleCompletionH0RingIso R p B).hom
    ((moduleCompletionH0Functor R (p : R)).map (ModuleCat.ofHom f)
      ((moduleCompletionH0RingIso R p A).inv
        (principalCompletionRingCatUnit p (CommRingCat.of A) x))) =
    principalCompletionLinearMap R p f (principalCompletionRingCatUnit p (CommRingCat.of A) x)
  rw [moduleCompletionH0RingIso_inv_unit, principalCompletionLinearMap_unit]
  have hn := ConcreteCategory.congr_hom
    ((moduleCompletionH0Unit R (p : R)).naturality (ModuleCat.ofHom f)) x
  change ((moduleCompletionH0Unit R (p : R)).app (ModuleCat.of R B)) (f x) =
    (moduleCompletionH0Functor R (p : R)).map (ModuleCat.ofHom f)
      (((moduleCompletionH0Unit R (p : R)).app (ModuleCat.of R A)) x) at hn
  rw [← hn]
  exact moduleCompletionH0RingIso_unit R p B (f x)

end SerrePositivity.DerivedCompletion
