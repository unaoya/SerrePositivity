module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModuleComplete
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleCochainCup
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModule
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModuleComplete
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass

/-!
# Hodge–Tate 比較の係数線形な余鎖模型

## 概要
既存の affine Hodge–Tate 作用を持つ余単体的加群と交代余面複体を公開する。

## 方針
HodgeTateModule の係数射と同じデータを使い、余輪体・cup 積との照合を移す。

## 規約
R = (A/d)⟨X₁,…,Xᵣ⟩。新しい係数作用や別の Hodge–Tate 写像は選ばない。

## 使われ方
BS 著者版 Proposition 6.2 の古典的な比較と、Lemma 4.22 の鎖複体模型への接続。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicTopology
open SerrePositivity.Cosimplicial SerrePositivity.HomologicalAlgebra
  SerrePositivity.DerivedCompletion
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
  (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- コホモロジー上の既存の係数作用を定めた、同じ項ごとの係数射。 -/
def affineHTCoefficients :
    (Functor.const SimplexCategory).obj (CommRingCat.of (affineAlgebra P r)) ⟶
      reducedModel P hP r := htCoefficients P hP r

/-- 公開した係数射は、元の項ごとの構造射そのものである。 -/
theorem affineHTCoefficients_app (n : SimplexCategory) :
    (affineHTCoefficients P hP r).app n = CommRingCat.ofHom (htSec P hP r n) := by
  rfl

/-- affine 係数環上の厳密な余単体的加群模型。 -/
abbrev affineHTModules : CosimplicialObject (ModuleCat.{u} (affineAlgebra P r)) :=
  toModules (affineAlgebra P r) (reducedModel P hP r) (affineHTCoefficients P hP r)

/-- 同じ余単体的加群の交代余面複体。 -/
abbrev affineHTComplex : CochainComplex (ModuleCat.{u} (affineAlgebra P r)) ℕ :=
  (alternatingCofaceMapComplex _).obj (affineHTModules P hP r)

/-- 係数線形な微分は元の加法的な Čech 微分そのものである。 -/
theorem affineHTComplex_d_apply (n : ℕ) (x : (affineHTComplex P hP r).X n) :
    (affineHTComplex P hP r).d n (n + 1) x =
      cochainDifferential (reducedModel P hP r) n x :=
  moduleCochains_d_apply (affineAlgebra P r) (reducedModel P hP r)
    (affineHTCoefficients P hP r) n x

/-- 元の余輪体を、同じ係数線形複体の cycles へ送る。 -/
def affineHTCycleRep (n : ℕ) (a : Cocycles (reducedModel P hP r) n) :
    (affineHTComplex P hP r).cycles n :=
  moduleCycleRep (affineAlgebra P r) (reducedModel P hP r)
    (affineHTCoefficients P hP r) n a

/-- cycles の包含を取ると元の代表元に戻る。 -/
theorem affineHTCycleRep_i (n : ℕ) (a : Cocycles (reducedModel P hP r) n) :
    (affineHTComplex P hP r).iCycles n (affineHTCycleRep P hP r n a) = a.1 :=
  moduleCycleRep_apply (affineAlgebra P r) (reducedModel P hP r)
    (affineHTCoefficients P hP r) n a

/-- 既存の Hodge–Tate 作用を用いる、係数線形なコホモロジー同型。 -/
def affineHTCohomologyEquiv (n : ℕ) :
    letI := htModule P hP r n
    hodgeTateCohomology' P hP r n ≃ₗ[affineAlgebra P r]
      (affineHTComplex P hP r).homology n :=
  (cohomologyEquivModuleHomology (affineAlgebra P r) (reducedModel P hP r)
    (affineHTCoefficients P hP r) n).linearEquiv (affineAlgebra P r)

/-- この同型は余輪体の同じ代表が定めるホモロジー類を取る。 -/
theorem affineHTCohomologyEquiv_class (n : ℕ)
    (a : Cocycles (reducedModel P hP r) n) :
    affineHTCohomologyEquiv P hP r n (cohomologyClass (reducedModel P hP r) n a) =
      (affineHTComplex P hP r).homologyπ n (affineHTCycleRep P hP r n a) :=
  cohomologyEquivModuleHomology_class (affineAlgebra P r) (reducedModel P hP r)
    (affineHTCoefficients P hP r) n a

/-- 係数線形模型上の既存の Alexander–Whitney 積。 -/
abbrev affineHTCup : CochainProduct (affineHTComplex P hP r) :=
  moduleCochainCup (affineAlgebra P r) (reducedModel P hP r)
    (affineHTCoefficients P hP r)

/-- コホモロジー同型は、既存の cup 積を同じ余鎖積へ移す。 -/
theorem affineHTCohomologyEquiv_cup {i j : ℕ}
    (a : hodgeTateCohomology' P hP r i) (b : hodgeTateCohomology' P hP r j) :
    affineHTCohomologyEquiv P hP r (i+j) (cohomologyCup (reducedModel P hP r) a b) =
      (affineHTCup P hP r).onHomology
        (affineHTCohomologyEquiv P hP r i a) (affineHTCohomologyEquiv P hP r j b) :=
  cohomologyEquivModuleHomology_cup (affineAlgebra P r) (reducedModel P hP r)
    (affineHTCoefficients P hP r) a b

/-- 各余単体項は、元の係数作用のまま導来 p 完備である。 -/
theorem affineHTModules_isModuleComplete (n : SimplexCategory) :
    IsModuleComplete (affineAlgebra P r) (p : affineAlgebra P r)
      ((affineHTModules P hP r).obj n) := htTerm_isModuleComplete P hP r n

/-- 複体のホモロジーも、同じ係数環上で導来 p 完備である。 -/
theorem affineHTComplex_homology_isModuleComplete (n : ℕ) :
    IsModuleComplete (affineAlgebra P r) (p : affineAlgebra P r)
      ((affineHTComplex P hP r).homology n) := by
  letI := htModule P hP r n
  exact isModuleComplete_of_linearEquiv (affineAlgebra P r) (p : affineAlgebra P r) _ _
    (affineHTCohomologyEquiv P hP r n) (htModule_isModuleComplete P hP r n)

end SerrePositivity.BhattScholze.Prismatic
