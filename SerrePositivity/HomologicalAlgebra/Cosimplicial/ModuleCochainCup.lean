module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.AWBilinear
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
public import SerrePositivity.HomologicalAlgebra.CochainProductClass
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.AWBilinear
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.HomologicalAlgebra.CochainProductClass

/-!
# 余単体的可換環の係数線形な余鎖積

## 概要
可換環の Alexander–Whitney 積を係数加群の余鎖積にし、コホモロジーの cup 積と照合する。

## 方針
係数線形の乗法は余単体構造射について自然。コホモロジーでは余輪体の代表で比較する。

## 規約
係数の作用は余単体への定数射から取る。

## 使われ方
pd Čech と pd de Rham の比較。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology HomologicalComplex
  SerrePositivity.HomologicalAlgebra
open scoped Simplicial

universe u

namespace SerrePositivity.Cosimplicial

variable (k : Type u) [CommRing k] (X : CosimplicialObject CommRingCat.{u})
variable (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ X)

local notation "Y" => toModules k X ι
local notation "K" => moduleCochains k X ι

private def termMul (n : SimplexCategory) : (Y).obj n →ₗ[k] (Y).obj n →ₗ[k] (Y).obj n :=
  letI : Algebra k (X.obj n) := (ι.app n).hom.toAlgebra
  LinearMap.mul k (X.obj n)

private theorem termMul_natural {a b : SimplexCategory} (θ : a ⟶ b)
    (x y : (Y).obj a) :
    (Y).map θ (termMul k X ι a x y) = termMul k X ι b ((Y).map θ x) ((Y).map θ y) := by
  let x' : X.obj a := x
  let y' : X.obj a := y
  exact map_mul (X.map θ).hom x' y'

set_option backward.isDefEq.respectTransparency false in
/-- 余単体的可換環の係数線形な Alexander–Whitney 余鎖積。 -/
def moduleCochainCup :
    CochainProduct ((alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (toModules k X ι)) where
  mul i j := (termMul k X ι ⦋i+j⦌).compl₁₂
    ((Y).map (frontFace i j)).hom ((Y).map (backFace i j)).hom
  leibniz i j x y := by
    have hd (n : ℕ) : (K).d n (n+1) = moduleCofaceDifferential Y n := by
      dsimp only [moduleCochains, alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
        CochainComplex.of]
      rw [CochainComplex.of_d]
      rfl
    rw [hd, hd, hd]
    exact moduleCofaceDifferential_awBilinear Y Y Y (termMul k X ι) (termMul_natural k X ι) x y

/-- 加法的コホモロジーと係数加群のコホモロジーの同型は cup 積を保つ。 -/
theorem cohomologyEquivModuleHomology_cup {i j : ℕ} (a : cohomology X i) (b : cohomology X j) :
    cohomologyEquivModuleHomology k X ι (i+j) (cohomologyCup X a b) =
      (moduleCochainCup k X ι).onHomology (cohomologyEquivModuleHomology k X ι i a)
        (cohomologyEquivModuleHomology k X ι j b) := by
  obtain ⟨a,rfl⟩ := cohomologyClass_surjective X i a
  obtain ⟨b,rfl⟩ := cohomologyClass_surjective X j b
  rw [cohomologyCup_class, cohomologyEquivModuleHomology_class,
    cohomologyEquivModuleHomology_class, cohomologyEquivModuleHomology_class]
  change @CochainProduct.closedClass k _ (K) (i+j) (cocycleCup X a b).1
      (moduleCycle k X ι (i+j) (cocycleCup X a b)) =
    (moduleCochainCup k X ι).onHomology
      (CochainProduct.closedClass i a.1 (moduleCycle k X ι i a))
      (CochainProduct.closedClass j b.1 (moduleCycle k X ι j b))
  exact (CochainProduct.onHomology_closedClass (moduleCochainCup k X ι) a.1 b.1
    (moduleCycle k X ι i a) (moduleCycle k X ι j b)
    (moduleCycle k X ι (i+j) (cocycleCup X a b))).symm

end SerrePositivity.Cosimplicial
