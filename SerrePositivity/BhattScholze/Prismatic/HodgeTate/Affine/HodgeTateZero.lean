module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# Hodge–Tate 写像の次数零

## 概要
affine 余単体模型の剰余の零次コホモロジーに、完備多項式環から写像を与える。

## 方針
各 prism の剰余への構造射が自然であることを、PrismOver の射の剰余環での可換条件から示す。

## 規約
次数零の積は cup 積で読む。

## 使われ方
多項式の場合の Hodge–Tate 写像の次数一と Bockstein。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
  (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- affine 模型の商の余単体コホモロジー。 -/
abbrev hodgeTateCohomology' (i : ℕ) := cohomology (reducedModel P hP r) i

/-- affine 模型で基底生成元を法とする Bockstein。 -/
def bockstein (i : ℕ) : hodgeTateCohomology' P hP r i →+ hodgeTateCohomology' P hP r (i+1) :=
  cupBockstein (htRings P hP r) (htGenerator P hP r) (htGenerator_nat P hP r)
    (htGenerator_regular P hP r) A (htBase P hP r) i

private theorem htSec_nat {m n : SimplexCategory} (θ : m ⟶ n) (x : affineAlgebra P r) :
    (reducedModel P hP r).map θ (htSec P hP r m x) = htSec P hP r n x := by
  let f := (htCech P hP r).map θ
  let e := htResidueIso P hP r m
  let E := htResidueIso P hP r n
  let a := htSec P hP r m x
  have hx : e a = ((htCech P hP r).obj m).sec x :=
    e.apply_symm_apply _
  have h := DFunLike.congr_fun f.comm_sec x
  apply E.injective
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective a
  have h₁ : E ((reducedModel P hP r).map θ a) = f.toHom.quotientMap (e a) := by
    rw [← hy]
    rfl
  rw [h₁, hx]
  exact h.trans (E.apply_symm_apply _).symm

/-- affine 係数環から二つの余面の等化部分環への射。 -/
def htSecZero : affineAlgebra P r →+* zeroCocycleRing (reducedModel P hP r) :=
  (htSec P hP r ⦋0⦌).codRestrict _ fun x =>
    (htSec_nat P hP r (SimplexCategory.δ (0 : Fin 2)) x).trans
      (htSec_nat P hP r (SimplexCategory.δ (1 : Fin 2)) x).symm

/-- Hodge–Tate 写像の次数零。 -/
def hodgeTateMapZero : affineAlgebra P r →+* hodgeTateCohomology' P hP r 0 :=
  (cohomologyZeroRingEquiv (reducedModel P hP r)).symm.toRingHom.comp (htSecZero P hP r)

end SerrePositivity.BhattScholze.Prismatic
