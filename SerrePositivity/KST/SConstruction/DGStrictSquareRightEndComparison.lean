module
public import SerrePositivity.KST.SConstruction.DGStrictSquareQuotientEnd
public import SerrePositivity.KST.SConstruction.DGGluingRightAxisEnd
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionFactorization
public import SerrePositivity.KST.SConstruction.DGClosedComparisonIso
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonContraction

/-! # 元の右 End 射の実 Perf 比較と指定商への因子分解
概要：元の右対象 End から指定商 End を通る射を、元の商への右軸射と照合する。
方針：同じ厳密 dg 因子分解を元の実 Perf 合成比較へ渡し、全 Hom 自然性を保つ。
規約：元の対象・商・射を固定。使われ方：指定 End の Morita 同定後の右端の射。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  {P : Type t} [DGCategory R P] (L : DGFunctor R P C) (G : DGFunctor R P D)
  (h : L.comp p = G.comp q) (zc : C)
  (hc : Limits.IsZero (ForgetEnrichment.of (Complex R) zc)) (b : D)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "j" => dgStrictSquareDiagonal R C D E p q L G h
local notation "I" => dgStrictSquareQuotientInput R C D E p q L G h zc hc b

/-- 元の右対象 End から、同じ標準対角商内の指定 End への実 dg 射。 -/
def dgStrictSquareRightQuotientEndMap :
    DGFunctor R (EndomorphismObject b) (I).endObject :=
  dgGluingRightQuotientEndMap R C D (M) zc hc (j) b

local notation "F" => dgStrictSquareRightQuotientEndMap R C D E p q L G h zc hc b
local notation "H" => DGFunctor.comp
  (DGFunctor.comp (endomorphismInclusion R b) (dgGluingRightAxis R C D (M) zc hc))
  (DGLaxQuotientEndInput.projection (I))

/-- 同じ右 End 射の商への因子分解は、元の右軸と商射を全 Hom で厳密に回収する。 -/
lemma dgStrictSquareRightQuotientEndMap_inclusion : (F).comp (I).endInclusion = (H) :=
  dgGluingRightQuotientEndMap_inclusion R C D (M) zc hc (j) b

/-- 元の右 End 射を指定商 End から二回延長した対象は、元の右軸商射の一回延長と同型。 -/
def dgStrictSquareRightEndPerfectAt (X : PerfectDGModule R (EndomorphismObject b)) :
    ForgetEnrichment.of (Complex R)
      (((perfectDGExtension R (EndomorphismObject b) (I).endObject (F)).comp
        (perfectDGExtension R (I).endObject (I).quotientObject (I).endInclusion)).obj X) ≅
    ForgetEnrichment.of (Complex R)
      ((perfectDGExtension R (EndomorphismObject b) (I).quotientObject (H)).obj X) :=
  perfectDGExtensionFactorizationAt R (EndomorphismObject b) (I).endObject
    (I).quotientObject (F) (I).endInclusion (H)
    (dgStrictSquareRightQuotientEndMap_inclusion R C D E p q L G h zc hc b) X

/-- 同じ右 End 射の実 Perf 比較は、全 Hom 複体上で自然。 -/
lemma dgStrictSquareRightEndPerfectAt_naturality
    (X Y : PerfectDGModule R (EndomorphismObject b)) :
    ((perfectDGExtension R (EndomorphismObject b) (I).endObject (F)).comp
      (perfectDGExtension R (I).endObject (I).quotientObject (I).endInclusion)).map X Y ≫
      eHomWhiskerLeft (Complex R) _
        (dgStrictSquareRightEndPerfectAt R C D E p q L G h zc hc b Y).hom =
    (perfectDGExtension R (EndomorphismObject b) (I).quotientObject (H)).map X Y ≫
      eHomWhiskerRight (Complex R)
        (dgStrictSquareRightEndPerfectAt R C D E p q L G h zc hc b X).hom _ :=
  perfectDGExtensionFactorizationAt_naturality R (EndomorphismObject b) (I).endObject
    (I).quotientObject (F) (I).endInclusion (H)
    (dgStrictSquareRightQuotientEndMap_inclusion R C D E p q L G h zc hc b) X Y

/-- 元の全 Hom 自然比較を、同じ成分の閉零自然同型に束ねる。 -/
def dgStrictSquareRightEndPerfectClosedIso :
    ((perfectDGExtension R (EndomorphismObject b) (I).endObject (F)).comp
      (perfectDGExtension R (I).endObject (I).quotientObject (I).endInclusion)).onClosed ≅
    (perfectDGExtension R (EndomorphismObject b) (I).quotientObject (H)).onClosed :=
  dgFunctorClosedComparisonIso R _ _
    (dgStrictSquareRightEndPerfectAt R C D E p q L G h zc hc b)
    (dgStrictSquareRightEndPerfectAt_naturality R C D E p q L G h zc hc b)

end SerrePositivity.KST.SConstruction
