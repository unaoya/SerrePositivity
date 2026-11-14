module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneGenerators
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCommutativity
import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero

/-!
# affine Hodge–Tate の零次 Bockstein の積公式

## 概要
零次 Hodge–Tate 写像と Bockstein の合成は affine 係数作用に関して導分の積公式を満たす。

## 方針
Bockstein の cup 積の Leibniz 則の次数零の場合と、cup 積の次数付き可換性を使う。

## 規約
係数の作用は零次からの左 cup 積。

## 使われ方
完備微分と Hodge–Tate 写像の一次の照合。
-/

public noncomputable section

open SerrePositivity.Cosimplicial
open scoped Simplicial

universe u

open CategoryTheory

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
private theorem bockstein_zero_product (C : CosimplicialObject CommRingCat.{u})
    (d : ∀ n : SimplexCategory, C.obj n)
    (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)
    (hd_reg : ∀ n, Function.Injective (fun x : C.obj n => d n * x))
    (k : Type u) [CommRing k]
    (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C)
    (a b : cohomology (quotPow C d hd_nat 1) 0) :
    let X := quotPow C d hd_nat 1
    let β := cupBockstein C d hd_nat hd_reg k ι
    β 0 (cohomologyCup X a b) =
      cohomologyCup X (β 0 a) b + cohomologyCup X a (β 0 b) := by
  dsimp only
  have h := bockstein_leibniz C d hd_nat hd_reg k ι 0 0 a b
  dsimp only at h
  rw [cast_eq, pow_zero, one_zsmul] at h
  exact h

private theorem cup_one_zero_comm (X : CosimplicialObject CommRingCat.{u})
    (a : cohomology X 1) (b : cohomology X 0) :
    cohomologyCup X a b = cohomologyCup X b a := by
  simpa only [cast_eq, Nat.mul_zero, pow_zero, one_zsmul] using cohomologyCup_comm X a b

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
  (hP : IsBoundedPrism P) (r : ℕ)

local notation "R" => affineAlgebra P r
local notation "H" => hodgeTateCohomology' P hP r 1
local notation "X" => reducedModel P hP r

local instance : Module R H := htModule P hP r 1

/-- 零次の affine 係数の Bockstein。 -/
def htBocksteinZero : R →+ H :=
  (bockstein P hP r 0).comp (hodgeTateMapZero P hP r).toAddMonoidHom

private theorem etaZero_mul (f g : R) :
    hodgeTateMapZero P hP r (f * g) =
      cohomologyCup X (hodgeTateMapZero P hP r f) (hodgeTateMapZero P hP r g) := by
  change cohomologyZeroAddEquiv X (htSecZero P hP r (f*g)) = _
  rw [map_mul]
  exact cohomologyZeroAddEquiv_mul X (htSecZero P hP r f) (htSecZero P hP r g)

set_option maxHeartbeats 800000 in
-- Bockstein と係数作用をそれぞれの余単体模型で照合する。
/-- 零次の affine 係数の Bockstein は Leibniz 則を満たす。 -/
theorem htBocksteinZero_mul (f g : R) :
    htBocksteinZero P hP r (f * g) =
      f • htBocksteinZero P hP r g + g • htBocksteinZero P hP r f := by
  let η := hodgeTateMapZero P hP r
  let β : hodgeTateCohomology' P hP r 0 →+ H := bockstein P hP r 0
  change β (η (f*g)) = f • β (η g) + g • β (η f)
  rw [etaZero_mul]
  have h := bockstein_zero_product (htRings P hP r) (htGenerator P hP r)
    (htGenerator_nat P hP r) (htGenerator_regular P hP r) A (htBase P hP r) (η f) (η g)
  have hcomm := cup_one_zero_comm X (β (η f)) (η g)
  have hf : f • β (η g) = cohomologyCup X (η f) (β (η g)) := by
    exact (htModuleData P hP r 1).property f _
  have hg : g • β (η f) = cohomologyCup X (η g) (β (η f)) := by
    exact (htModuleData P hP r 1).property g _
  rw [hf, hg, ← hcomm, add_comm]
  exact h

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- 基底の剰余の定数は整係数の定数余輪体へ持ち上がる。 -/
theorem htBocksteinZero_algebraMap (c : A ⧸ P.ideal) :
    htBocksteinZero P hP r (algebraMap (A ⧸ P.ideal) R c) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  let C := htRings P hP r
  let i := htBase P hP r
  let n : SimplexCategory := ⦋0⦌
  let q := quotProjection C (htGenerator P hP r) (htGenerator_nat P hP r) 1
  let x : C.obj n := i.app n a
  let f := algebraMap (A ⧸ P.ideal) R (Ideal.Quotient.mk P.ideal a)
  let z := zeroCocyclesEquiv X (htSecZero P hP r f)
  have hz : hodgeTateMapZero P hP r f = cohomologyClass X 0 z := rfl
  have h₀ : q.app n x = z.1 := by
    let Y := (htCech P hP r).obj n
    let E := htResidueIso P hP r n
    change q.app n x = htSec P hP r n f
    apply E.injective
    have hs := DFunLike.congr_fun Y.sec_comp (Ideal.Quotient.mk P.ideal a)
    change Y.sec f = Ideal.Quotient.mk Y.Q.ideal x at hs
    change Ideal.Quotient.mk Y.Q.ideal x = E (E.symm (Y.sec f))
    rw [E.apply_symm_apply, hs]
  have hC (j : Fin 2) : C.map (SimplexCategory.δ j) x = i.app ⦋1⦌ a := by
    have h := i.naturality (SimplexCategory.δ j)
    change 𝟙 (CommRingCat.of A) ≫ i.app ⦋1⦌ = i.app ⦋0⦌ ≫ C.map (SimplexCategory.δ j) at h
    rw [Category.id_comp] at h
    exact ConcreteCategory.congr_hom h.symm a
  have hD : cochainDifferential C 0 x = htGenerator P hP r ⦋1⦌ * 0 := by
    rw [cochainDifferential_zero, hC, hC, sub_self, mul_zero]
  change bockstein P hP r 0 (hodgeTateMapZero P hP r f) = 0
  rw [hz]
  have h := cupBockstein_class C (htGenerator P hP r) (htGenerator_nat P hP r)
    (htGenerator_regular P hP r) A i 0 z 0 x 0 h₀ (map_zero _) hD
  exact h.trans (map_zero _)

end SerrePositivity.BhattScholze.Prismatic
