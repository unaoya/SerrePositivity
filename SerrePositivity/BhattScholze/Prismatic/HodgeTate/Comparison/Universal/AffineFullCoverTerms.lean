module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCone
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeDerivedBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCover
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 元の full envelope 行の Construction 6.1 での完備導来底変換

## 概要
元の full envelope の基底上の台加群の完備導来底変換を、被覆上の元の full envelope に同定する。

## 方針
元の小さい包の項ごとの指定同型を、元の htRings と htBase の型で読む。

## 規約
基底の通常の平坦性を仮定しない。剰余行と Tot への接続は別に必要となる。

## 使われ方
元の full envelope の正則商の錐表示と、被覆上の元の模型の比較。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の full envelope 行の二座標完備導来底変換は、被覆上の元の行を計算する。 -/
def affineFullCoverTermIso (n : SimplexCategory) :
    (pairCompletedBaseChange (Construction61.crystallineCoverMap P).toRingHom
      (p : Construction61.crystallineCoverRing P) (p : Construction61.crystallineCoverRing P)
      (boundedAboveDerivedSingleFunctor.obj ((affineFullBaseModules P hP r).obj n))).obj ≅
        (moduleObjectFunctor (Construction61.crystallineCoverRing P)).obj
          ((affineFullBaseModules (Construction61.crystallineCover P)
            (Construction61.crystallineCover_bounded P) r).obj n) := by
  exact affineEnvelopeTermCompletedBaseChangeToTargetIso P (Construction61.crystallineCover P)
    hP (Construction61.crystallineCover_bounded P) (Construction61.crystallineCoverMap P)
    r n.len (cutoff A (affineAlgebra P r)) le_rfl
    (cutoff (Construction61.crystallineCoverRing P) (affineAlgebra (Construction61.crystallineCover P) r))
    le_rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
