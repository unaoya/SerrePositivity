module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModule

/-!
# 元の affine コホモロジーの係数作用の類による表示

## 概要
元の係数作用を、同じ余輪体の項ごとの係数積の類で計算する。

## 方針
元のコホモロジー同型の線形性と、元の余輪体の包含で照合する。

## 規約
元の htModule の作用と、元の affineHTCoefficients の構造射を使う。

## 使われ方
向きの単位による Bockstein の係数を、標準 HT 写像の係数作用で読む。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic
open SerrePositivity.Cosimplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r i : ℕ)

/-- 同じ余輪体に項ごとの係数を掛けた類が、元のコホモロジーの係数作用である。 -/
theorem affineHTCohomology_smul_class (a : affineAlgebra P r)
    (c c' : Cocycles (reducedModel P hP r) i)
    (hc : (show (reducedModel P hP r).obj ⦋i⦌ from c'.1) =
      (affineHTCoefficients P hP r).app ⦋i⦌ a *
        (show (reducedModel P hP r).obj ⦋i⦌ from c.1)) :
    letI := htModule P hP r i
    a • cohomologyClass (reducedModel P hP r) i c = cohomologyClass (reducedModel P hP r) i c' := by
  letI := htModule P hP r i
  have he : a • affineHTCycleRep P hP r i c = affineHTCycleRep P hP r i c' := by
    apply (ModuleCat.mono_iff_injective ((affineHTComplex P hP r).iCycles i)).mp inferInstance
    rw [map_smul, affineHTCycleRep_i, affineHTCycleRep_i]
    exact hc.symm
  apply (affineHTCohomologyEquiv P hP r i).injective
  rw [map_smul, affineHTCohomologyEquiv_class, affineHTCohomologyEquiv_class, ← map_smul, he]

end SerrePositivity.BhattScholze.Prismatic
