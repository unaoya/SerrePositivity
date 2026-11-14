module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CupProduct
import Mathlib.Algebra.Module.TransferInstance
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# affine Hodge–Tate コホモロジーの係数作用

## 概要
余単体的な剰余環のコホモロジーに affine 係数環を作用させる。

## 方針
各項の自然な係数作用を加群のコホモロジーから移す。

## 規約
作用は零次の Hodge–Tate 写像の像を左から cup することに一致する。

## 使われ方
Hodge–Tate 写像の次数一と外積への延長。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
  (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

local notation "X" => reducedModel P hP r
local notation "R" => affineAlgebra P r

private def htCoefficients : (Functor.const SimplexCategory).obj (CommRingCat.of R) ⟶ X where
  app n := CommRingCat.ofHom (htSec P hP r n)
  naturality m n θ := by
    change 𝟙 (CommRingCat.of R) ≫ CommRingCat.ofHom (htSec P hP r n) = _
    rw [Category.id_comp]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (htSec_nat P hP r θ x).symm

@[instance_reducible] private def htModuleAux (n : ℕ) : Module R (cohomology X n) :=
  (cohomologyEquivModuleHomology R X (htCoefficients P hP r) n).module R

private theorem class_cast {Y : CosimplicialObject CommRingCat.{u}} {a b : ℕ} (h : a = b)
    (x : Cocycles Y a) :
    cast (congrArg (cohomology Y) h) (cohomologyClass Y a x) =
      cohomologyClass Y b (cast (congrArg (fun n => ↥(Cocycles Y n)) h) x) := by
  subst b
  rfl

private theorem val_cast {Y : CosimplicialObject CommRingCat.{u}} {a b : ℕ} (h : a = b)
    (x : Cocycles Y a) :
    (cast (congrArg (fun n => ↥(Cocycles Y n)) h) x).1 =
      cast (congrArg (fun n => (Y.obj ⦋n⦌ : Type u)) h) x.1 := by
  subst b
  rfl

private theorem htSec_cup_zero (c : R) (n : ℕ) (x : (X).obj ⦋n⦌) :
    cast (congrArg (fun i => ((X).obj ⦋i⦌ : Type u)) (Nat.zero_add n))
      (cup X (htSec P hP r ⦋0⦌ c) x) = htSec P hP r ⦋n⦌ c * x := by
  rw [cast_obj, cup, map_mul, htSec_nat, htSec_nat]
  congr 1
  have h : backFace 0 n ≫ eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n)) = 𝟙 ⦋n⦌ := by
    ext i
    simp [backFace]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, h]
  · exact ConcreteCategory.congr_hom ((X).map_id ⦋n⦌) x
  · exact Nat.zero_add n

private theorem htModuleAux_action (n : ℕ) (c : R) (x : cohomology X n) :
    letI := htModuleAux P hP r n
    c • x = cast (congrArg (cohomology X) (Nat.zero_add n))
      (cohomologyCup X (hodgeTateMapZero P hP r c) x) := by
  let := htModuleAux P hP r n
  obtain ⟨a, rfl⟩ := cohomologyClass_surjective X n x
  let i := htCoefficients P hP r
  let E := cohomologyEquivModuleHomology R X i n
  apply E.injective
  let a₀ := zeroCocyclesEquiv X (htSecZero P hP r c)
  have hz : hodgeTateMapZero P hP r c = cohomologyClass X 0 a₀ := rfl
  rw [hz, cohomologyCup_class, class_cast, cohomologyEquivModuleHomology_class]
  have h := cohomologyEquivModuleHomology_class R X i n a
  have hE := (E.linearEquiv R).map_smul c (cohomologyClass X n a)
  change E (c • cohomologyClass X n a) = c • E (cohomologyClass X n a) at hE
  rw [hE, h, ← map_smul]
  congr 1
  apply (ModuleCat.mono_iff_injective ((moduleCochains R X i).iCycles n)).mp inferInstance
  rw [map_smul, moduleCycleRep_apply, moduleCycleRep_apply, val_cast]
  let x : (X).obj ⦋n⦌ := a.1
  change htSec P hP r ⦋n⦌ c * x = cast _ (cup X (htSec P hP r ⦋0⦌ c) x)
  exact (htSec_cup_zero P hP r c n x).symm
  all_goals exact Nat.zero_add n

/-- affine 係数の作用を cup 積で表す。 -/
def htModuleData (n : ℕ) :
    { M : Module R (hodgeTateCohomology' P hP r n) //
      letI := M
      ∀ (a : R) (z : hodgeTateCohomology' P hP r n),
        a • z = cast (by simp) (cohomologyCup X (hodgeTateMapZero P hP r a) z) } :=
  ⟨htModuleAux P hP r n, htModuleAux_action P hP r n⟩

/-- affine 模型のコホモロジー上の係数加群。 -/
abbrev htModule (n : ℕ) := (htModuleData P hP r n).val

end SerrePositivity.BhattScholze.Prismatic
