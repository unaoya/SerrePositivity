module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationProduct

/-!
概要：付値試験環の積の正次数のČech項に、第0因子からの指定係数射を入れる。
方針：既存のunderCechInclusionを使い、Underの可換三角形を環準同型として読む。
規約：別の代数構造を選ばず、元の基底射との合成を同じ脚で保つ。
使われ方：2iのP03・P04、B1の正次数の底変換への係数の接続。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped Simplicial
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画P03：同じ余積の第0因子の脚。 -/
def probeCechFirstFactor {A : Type u} [CommRing A] (n : ℕ) :
    (∀ t : Arc.ValuationProbeIndex A, Arc.ValuationProbe A t) →+*
      ((Cech.underCech (Under.mk (CommRingCat.ofHom
        (Arc.valuationProbeProductMap A)))).right.obj ⦋n⦌).right :=
  (Cech.underCechInclusion (Under.mk (CommRingCat.ofHom
    (Arc.valuationProbeProductMap A))) ⦋n⦌ 0).right.hom

/-- 計画P04：元の基底射との合成は同じČech項の構造射。 -/
theorem probeCechFirstFactor_comp {A : Type u} [CommRing A] (n : ℕ) :
    (probeCechFirstFactor (A := A) n).comp (Arc.valuationProbeProductMap A) =
      ((Cech.underCech (Under.mk (CommRingCat.ofHom
        (Arc.valuationProbeProductMap A)))).right.obj ⦋n⦌).hom.hom := by
  exact congrArg CommRingCat.Hom.hom (Under.w (Cech.underCechInclusion
    (Under.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A))) ⦋n⦌ 0))

/-- 計画P05：同じ第0因子の係数射で、B1の正次数への底変換を比較する。 -/
def probeChangeToTermIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) :
    Cech.changeToTerm (Under.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A)))
      (Under.mk (CommRingCat.ofHom f)) (n + 1) ≅
    Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom
      (arcBaseChangeHom f (Arc.valuationProbeProductMap A))
      (probeCechFirstFactor (A := A) n))) := by
  let R := Under.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A))
  let D := (Cech.underCech R).right.obj ⦋n⦌
  change Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom f D.hom.hom)) ≅ _
  exact arcBaseChangeTransIso f (Arc.valuationProbeProductMap A)
    (probeCechFirstFactor (A := A) n) D.hom.hom (probeCechFirstFactor_comp n)

end SerrePositivity.AlgebraicGeometry.ArcRouteB
