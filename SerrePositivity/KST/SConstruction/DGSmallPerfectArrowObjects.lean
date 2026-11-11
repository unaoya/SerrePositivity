module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectArrow
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeFreeComparison

/-! # 元の実延長像を含む終域の零対象と代表対象
概要：終域小模型の指定零加群・代表加群と、元の延長の自由代表比較を保持する。
方針：既存の実像包含模型の指定対象と比較をそのまま使う。
規約：対象の選び直しをしない。使われ方：実対角商の零左成分と指定右対象。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
  (C : Type w) [DGCategory R C] [Small.{u} C] (L : DGFunctor R P C)
local notation "Y" => dgSmallPerfectEnvelopeExtensionFamily R P C Empty
  (dgSmallPerfectBaseFamily R P) L

/-- 同じ元の実零加群を保持する、終域の指定零対象。 -/
def dgSmallPerfectArrowTargetZero : DGSmallPerfectArrowTarget R P C L :=
  dgSmallPerfectEnvelopeZero R C (DGSmallPerfectBase R P) (Y)

/-- 同じ元の代表加群を保持する、終域の指定対象。 -/
def dgSmallPerfectArrowTargetRepresentable (c : C) : DGSmallPerfectArrowTarget R P C L :=
  dgSmallPerfectEnvelopeRepresentable R C (DGSmallPerfectBase R P) (Y) c

/-- 同じ指定零加群は、終域の閉零射圏で実零対象。 -/
lemma dgSmallPerfectArrowTargetZero_isZero :
    IsZero (ForgetEnrichment.of (Complex R) (dgSmallPerfectArrowTargetZero R P C L)) :=
  dgSmallPerfectEnvelopeZero_isZero R C (DGSmallPerfectBase R P) (Y)

/-- 同じ実延長像を保持する終域の native nerve は安定。 -/
lemma dgSmallPerfectArrowTargetNerve_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGSmallPerfectArrowTarget R P C L)) :=
  dgSmallPerfectEnvelopeNerve_isStable R C (DGSmallPerfectBase R P) (Y)

/-- 元の実延長の自由代表比較を、同じ小模型の指定代表で回収する。 -/
def dgSmallPerfectArrowRepresentableIso (a : P) :
    ForgetEnrichment.of (Complex R)
      ((dgSmallPerfectArrow R P C L).obj (dgSmallPerfectBaseRepresentable R P a)) ≅
    ForgetEnrichment.of (Complex R) (dgSmallPerfectArrowTargetRepresentable R P C L (L.obj a)) :=
  dgSmallPerfectEnvelopeExtensionRepresentableIso R P C Empty (dgSmallPerfectBaseFamily R P) L a

end SerrePositivity.KST.SConstruction
