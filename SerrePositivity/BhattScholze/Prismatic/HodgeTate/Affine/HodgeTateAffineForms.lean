module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
public import SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
public import SerrePositivity.CommutativeAlgebra.DeRham.CompletedWedge
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# Hodge–Tate 写像の affine 微分形式

## 概要
完備多項式環と完備微分形式を、変数の宇宙をそろえて比較する。

## 方針
多項式の添字同型を完備化に移し、次数零の外冪を係数環と同一視する。

## 規約
比較の定義域は完備微分形式を使う。

## 使われ方
Hodge–Tate 写像の定義と結晶基底での Cartier 比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- 微分形式の変数を係数環と同じ宇宙に置く。 -/
abbrev formVars (r : ℕ) := ULift.{u} (Fin r)

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (r : ℕ)

local notation "k" => (A ⧸ P.ideal)
local notation "T" => formVars r
local notation "B" => DeRham.Poly k T
local notation "Q" => DeRham.completedPoly k T p

/-- 変数を持ち上げた完備微分形式。 -/
abbrev affineForms (i : ℕ) := DeRham.completedForms k (formVars.{u} r) p i

/-- 変数の持ち上げに沿う affine 係数環の同型。 -/
def affineCoordinateIso : affineAlgebra P r ≃+* Q :=
  ((principalCompletionRingFunctor p).mapIso
    (MvPolynomial.renameEquiv k (Equiv.ulift.symm : Fin r ≃
      formVars.{u} r)).toRingEquiv.toCommRingCatIso).commRingCatIsoToRingEquiv

/-- 多項式の各変数の完備化単位は、持ち上げた変数の単位へ移る。 -/
theorem affineCoordinateIso_X (t : Fin r) :
    affineCoordinateIso P r (prismPolynomialUnit P (Fin r) (MvPolynomial.X t)) =
      algebraMap B Q (MvPolynomial.X (ULift.up t)) := by
  let e := MvPolynomial.renameEquiv k (Equiv.ulift.symm : Fin r ≃ formVars.{u} r)
  have h := ConcreteCategory.congr_hom
    (ringCatMap_comp_unit p e.toRingEquiv.toCommRingCatIso.hom) (MvPolynomial.X t)
  exact h.trans (congrArg (algebraMap B Q) (MvPolynomial.rename_X _ _))

instance affineFormsModule (i : ℕ) : Module (affineAlgebra P r) (affineForms P r i) :=
  Module.compHom _ (affineCoordinateIso P r).toRingHom

private def polynomialZeroForm : B ≃ₗ[B] DeRham.forms k T 0 :=
  { __ := DeRham.formsZeroEquiv k T
    map_smul' := fun c x => by
      have h (y : B) : DeRham.formsZeroEquiv k T y =
          y ⊗ₜ[k] (exteriorPower.zeroEquiv k (T → k)).symm 1 := by
        simp [DeRham.formsZeroEquiv]
      change DeRham.formsZeroEquiv k T (c • x) = c • DeRham.formsZeroEquiv k T x
      rw [h, h]
      rfl }

private def completeZeroForm : Q ≃ₗ[Q] affineForms P r 0 :=
  (TensorProduct.AlgebraTensorModule.rid B Q Q).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q Q) (polynomialZeroForm P r))

/-- 次数零の完備微分形式は係数環と同一視される。 -/
def degreeZeroForm : affineAlgebra P r ≃ₗ[affineAlgebra P r] affineForms P r 0 where
  __ := (affineCoordinateIso P r).toAddEquiv.trans (completeZeroForm P r).toAddEquiv
  map_smul' c x := by
    change completeZeroForm P r (affineCoordinateIso P r (c * x)) =
      affineCoordinateIso P r c • completeZeroForm P r (affineCoordinateIso P r x)
    rw [map_mul, ← smul_eq_mul, map_smul]

/-- affine 微分形式の完備 de Rham 微分。 -/
abbrev affineD (i : ℕ) := DeRham.completedDeRhamD k (formVars.{u} r) p i

/-- affine 微分形式の完備外積。 -/
abbrev affineWedge {i j : ℕ} := @DeRham.completedWedge k _ (formVars.{u} r) _ _ p i j

end SerrePositivity.BhattScholze.Prismatic
