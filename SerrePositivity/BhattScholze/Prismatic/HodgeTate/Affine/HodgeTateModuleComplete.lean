module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModule
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModule
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# affine Hodge–Tate コホモロジーの p 完備性

## 概要
商 Čech 模型の各項の導来 p 完備性から、係数加群のコホモロジーの完備性を得る。

## 方針
完備加群の間の線形写像の核と余核が完備なことを使う。

## 規約
係数作用は次数零の Hodge–Tate 写像との左 cup 積。

## 使われ方
完備多項式の Hodge–Tate 写像の生成元による判定。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
  (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

local notation "R" => affineAlgebra P r
local notation "X" => reducedModel P hP r
local notation "ι" => htCoefficients P hP r

private theorem htTerm_isModuleComplete (n : SimplexCategory) :
    IsModuleComplete R (p : R) ((toModules R X ι).obj n) := by
  let B := (htCech P hP r |>.obj n).B
  let Q := (htCech P hP r |>.obj n).Q
  let T := B ⧸ Q.ideal
  let f := (htCech P hP r |>.obj n).sec
  let := f.toAlgebra
  have hc : IsModuleComplete R (p : R) (ModuleCat.of R T) := by
    apply (isModuleComplete_algebraMap_iff R T (p : R) T).mp
    change IsModuleComplete T (f (p : R)) (ModuleCat.of T T)
    rw [map_natCast]
    exact isModuleComplete_principal_quotient_natCast B p Q.generator Q.complete_p
  let e := htResidueIso P hP r n
  let E : ((toModules R X ι).obj n) ≃ₗ[R] T :=
    { __ := e.toAddEquiv
      map_smul' := fun c x => by
        change (X).obj n at x
        change e (htSec P hP r n c * x) = f c * e x
        rw [map_mul]
        exact congrArg (fun t => t * e x) (e.apply_symm_apply _) }
  exact isModuleComplete_of_linearEquiv R (p : R) _ _ E.symm hc

private theorem homology_isModuleComplete {k : Type u} [CommRing k] (q : k)
    (K : CochainComplex (ModuleCat.{u} k) ℕ) (h : ∀ n, IsModuleComplete k q (K.X n)) (n : ℕ) :
    IsModuleComplete k q (K.homology n) := by
  let S := K.sc n
  let ec := S.cyclesIsoKernel ≪≫ ModuleCat.kernelIsoKer S.g
  have hc : IsModuleComplete k q S.cycles :=
    isModuleComplete_of_linearEquiv k q _ _ ec.symm.toLinearEquiv
      (isModuleComplete_ker k q S.g.hom (h _) (h _))
  let e := S.homologyIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel S.toCycles) ≪≫
    ModuleCat.cokernelIsoRangeQuotient S.toCycles
  exact isModuleComplete_of_linearEquiv k q _ _ e.symm.toLinearEquiv
    (isModuleComplete_coker k q S.toCycles.hom (h _) hc)

/-- affine Hodge–Tate のコホモロジー加群は導来 p 完備。 -/
theorem htModule_isModuleComplete (n : ℕ) :
    letI := htModule P hP r n
    IsModuleComplete R (p : R) (ModuleCat.of R (hodgeTateCohomology' P hP r n)) := by
  let := htModule P hP r n
  let K := (alternatingCofaceMapComplex (ModuleCat.{u} R)).obj (toModules R X ι)
  have h := homology_isModuleComplete (p : R) K
    (fun i => htTerm_isModuleComplete P hP r ⦋i⦌) n
  let e := cohomologyEquivModuleHomology R X ι n
  exact isModuleComplete_of_linearEquiv R (p : R) _ _ (e.linearEquiv R).symm h

end SerrePositivity.BhattScholze.Prismatic
