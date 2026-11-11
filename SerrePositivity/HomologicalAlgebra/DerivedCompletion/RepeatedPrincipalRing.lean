module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 同じ主元を二回並べた完備環

## 概要
二座標 (p,p) の完備化の H⁰ は、主元 p の完備環と標準的に同型になる。

## 方針
両者の完備環への延長の普遍性から互いに逆な射を作る。

## 規約
元の環上の代数同型と単位の式を固定する。正則性は仮定しない。

## 使われ方
BS 著者版 Theorem 6.4、結晶的な基底における二座標完備テンソルの表示。
-/

public noncomputable section
open CategoryTheory
universe u
namespace SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (R : Type u) [CommRing R]
attribute [local instance] pdCompletionCommRing pdCompletionAlgebra
local notation "P" => PDCompletionH0 R p (p : R)
local notation "j" => pdCompletionUnit R p (p : R)
local notation "i" => CommRingCat.Hom.hom (principalCompletionRingCatUnit p (CommRingCat.of R))

private def principalToRepeated : CompletedRing p R →+* P :=
  principalCompletionLift R (p : R) P (j) (pdCompletionH0_isComplete_p R p (p : R))

private theorem principalToRepeated_unit : (principalToRepeated p R).comp (i) = (j) :=
  principalCompletionLift_comp R (p : R) P (j) (pdCompletionH0_isComplete_p R p (p : R))

private def repeatedToPrincipal : P →+* CompletedRing p R :=
  (pdCompletion_existsUnique_ringHom R p (p : R) (CompletedRing p R) (i)
    (principalCompletion_isModuleComplete_unit (p : R))
    (principalCompletion_isModuleComplete_unit (p : R))).choose

private theorem repeatedToPrincipal_unit : (repeatedToPrincipal p R).comp (j) = (i) :=
  (pdCompletion_existsUnique_ringHom R p (p : R) (CompletedRing p R) (i)
    (principalCompletion_isModuleComplete_unit (p : R))
    (principalCompletion_isModuleComplete_unit (p : R))).choose_spec.1

private theorem repeated_principal_identity :
    (repeatedToPrincipal p R).comp (principalToRepeated p R) = RingHom.id (CompletedRing p R) := by
  apply (principalCompletion_existsUnique_ringHom R (p : R) (CompletedRing p R) (i)
    (principalCompletion_isModuleComplete_unit (p : R))).unique
  · change ((repeatedToPrincipal p R).comp (principalToRepeated p R)).comp (i) = (i)
    rw [RingHom.comp_assoc, principalToRepeated_unit, repeatedToPrincipal_unit]
  · rfl

private theorem principal_repeated_identity :
    (principalToRepeated p R).comp (repeatedToPrincipal p R) = RingHom.id P := by
  apply (pdCompletion_existsUnique_ringHom R p (p : R) P (j)
    (pdCompletionH0_isComplete_p R p (p : R))
    (pdCompletionH0_isComplete_p R p (p : R))).unique
  · rw [RingHom.comp_assoc, repeatedToPrincipal_unit, principalToRepeated_unit]
  · rfl

/-- (p,p) の完備化と p の主完備環を、標準写像を保って同定する。 -/
def repeatedPrincipalRingEquiv : P ≃+* CompletedRing p R :=
  RingEquiv.ofRingHom (repeatedToPrincipal p R) (principalToRepeated p R)
    (repeated_principal_identity p R) (principal_repeated_identity p R)

/-- 同型は元の環からの二つの単位を合わせる。 -/
theorem repeatedPrincipalRingEquiv_unit (x : R) :
    repeatedPrincipalRingEquiv p R ((j) x) = (i) x :=
  RingHom.congr_fun (repeatedToPrincipal_unit p R) x

/-- 同じ主元の二座標完備環と主完備環の、元の環上の代数同型。 -/
def repeatedPrincipalAlgEquiv : P ≃ₐ[R] CompletedRing p R :=
  { repeatedPrincipalRingEquiv p R with
    commutes' := repeatedPrincipalRingEquiv_unit p R }

end SerrePositivity.DerivedCompletion
