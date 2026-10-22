module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectBase
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeExtension

/-! # 元の実 Perf 始域から延長像を保持する終域への厳密 dg 射
概要：元の始域の全実対象の像を終域へ加え、元の実 graph 延長を保持する。
方針：空追加族による始域に、構成済みの厳密な実延長制限を適用する。
規約：同型な代表への選び直しをしない。使われ方：実 LT 四角形の左右二辺。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
  (C : Type w) [DGCategory R C] [Small.{u} C] (L : DGFunctor R P C)

/-- 同じ元の実延長像を全て含む終域の小さい実模型。 -/
abbrev DGSmallPerfectArrowTarget :=
  DGSmallPerfectEnvelopeExtensionTarget R P C Empty (dgSmallPerfectBaseFamily R P) L

/-- 同じ元の実 graph 延長を保つ、具体的小模型間の厳密 dg 関手。 -/
def dgSmallPerfectArrow :
    DGFunctor R (DGSmallPerfectBase R P) (DGSmallPerfectArrowTarget R P C L) :=
  dgSmallPerfectEnvelopeExtension R P C Empty (dgSmallPerfectBaseFamily R P) L

/-- 同じ終域から元の全 Perf への全 Hom を保つ包含。 -/
def dgSmallPerfectArrowTargetInclusion :
    DGFunctor R (DGSmallPerfectArrowTarget R P C L) (PerfectDGModule R C) :=
  dgSmallPerfectEnvelopeInclusion R C (DGSmallPerfectBase R P)
    (dgSmallPerfectEnvelopeExtensionFamily R P C Empty (dgSmallPerfectBaseFamily R P) L)

/-- 終域への包含後に、元の実延長を対象と全 Hom で厳密に回収する。 -/
lemma dgSmallPerfectArrow_inclusion :
    (dgSmallPerfectArrow R P C L).comp (dgSmallPerfectArrowTargetInclusion R P C L) =
    (dgSmallPerfectEnvelopeInclusion R P Empty (dgSmallPerfectBaseFamily R P)).comp
      (perfectDGExtension R P C L) :=
  dgSmallPerfectEnvelopeExtension_inclusion R P C Empty (dgSmallPerfectBaseFamily R P) L

end SerrePositivity.KST.SConstruction
