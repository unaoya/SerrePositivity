module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullCoverTerms
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDelta
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittAffineBaseChange

/-!
# 元のfull envelopeの基底上のp完備性

## 概要
元のfull envelopeの基底上の台加群はpについて完備である。

## 方針
元の標準包の完備自由δ環としての記述から、同じ元の基底脚で完備性を制限する。

## 規約
生成元がpであることは仮定せず、元のpの座標を保つ。

## 使われ方
元のfull envelopeの係数射を完備化単位に沿って一意に延長する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元のfull envelopeの行は、同じ基底のpについて完備。 -/
theorem affineFullBaseModules_complete_p
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    IsModuleComplete A (p : A) ((affineFullBaseModules P hP r).obj n) := by
  let T : Type u := (htRings P hP r).obj n
  letI : Algebra A T := ((htBase P hP r).app n).hom.toAlgebra
  have hT : IsModuleComplete T (p : T) (ModuleCat.of T T) := by
    exact completedFreeDelta_complete_p P (AffineIndex.{u} r n.len)
  apply (isModuleComplete_algebraMap_iff A T (p : A) T).mp
  simpa only [map_natCast] using hT

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
