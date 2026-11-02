module
public import SerrePositivity.KST.SConstruction.DGOdotTargetContracted
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration

/-! # 元の対角商から終域 cone への実 dg 延長
概要：元の指定収縮を使い、同じ対角商と指定 End から実終域への dg 関手を構成する。
方針：D β3 の既存 extension と既存の指定 End 制限を読み取り専用で適用する。
規約：商・局所化の普遍性を新設しない。使われ方：具体的 ⊙ の実比較射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 同じ実対角商から、元の実比較 cone の Perf 標的への dg 延長。 -/
def dgOdotTargetQuotientFunctor :
    DGFunctor R (dgOdotQuotientInput R d).quotientObject
      (PerfectDGModule R (DGOdotCorner R d)) :=
  DGQuotient.extension R (dgOdotTargetContractedFunctor R d)

/-- 同じ商延長は、元の射影との合成で元の実 cone 関手を厳密に回収する。 -/
lemma dgOdotTargetQuotientFunctor_original :
    (dgOdotQuotientInput R d).projection.comp (dgOdotTargetQuotientFunctor R d) =
      dgOdotTargetFunctor R d :=
  DGQuotient.inclusion_comp_extension R (dgOdotTargetContractedFunctor R d)

/-- 同じ商延長の対象像は、元の gluing 対象の同じ実比較 cone。 -/
lemma dgOdotTargetQuotientFunctor_obj (X : (dgOdotQuotientInput R d).quotientObject) :
    (dgOdotTargetQuotientFunctor R d).obj X = dgOdotTargetCone R d X.val := rfl

/-- 同じ商延長は元の ε を同じ指定収縮へ送る。 -/
lemma dgOdotTargetQuotientFunctor_epsilon
    (b : dgQuotientImage R (dgOdotQuotientInput R d).diagonal) :
    ((dgOdotTargetQuotientFunctor R d).map ⟨b.val⟩ ⟨b.val⟩).f (-1)
        (DGQuotient.epsilonElement R (DGOdotGluing R d)
          (dgQuotientImage R (dgOdotQuotientInput R d).diagonal) b) =
      (dgOdotTargetContractedFunctor R d).homotopy b :=
  DGQuotient.quotientEvaluation_epsilon R (dgOdotTargetContractedFunctor R d) b

/-- 元の指定商 End から、同じ指定右対象の実 cone End への dg 比較射。 -/
def dgOdotTargetQuotientEndMap :
    DGFunctor R (DGOdotQuotientEnd R d)
      (EndomorphismObject (dgOdotTargetCone R d (dgOdotQuotientInput R d).point)) :=
  pointedDGQuotientEndExtension R (dgOdotQuotientInput R d).diagonal
    (dgOdotTargetContractedFunctor R d) (dgOdotQuotientInput R d).point

/-- 同じ End 比較射は、元の商 End の全 path と指定 ε の評価そのもの。 -/
lemma dgOdotTargetQuotientEndMap_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotTargetQuotientEndMap R d).map x y =
      DGQuotient.quotientEvaluation R (dgOdotTargetContractedFunctor R d)
        (dgOdotQuotientInput R d).point (dgOdotQuotientInput R d).point := rfl

/-- 元の End 射は、同じ指定商 End 比較を経由して全 Hom 上で厳密に回収される。 -/
lemma dgOdotTargetQuotientEndMap_original :
    (dgOdotQuotientInput R d).endUnitMap.comp (dgOdotTargetQuotientEndMap R d) =
      endomorphismMap R (dgOdotTargetFunctor R d) (dgOdotQuotientInput R d).point :=
  pointedDGQuotientEndExtension_unitMap R (dgOdotQuotientInput R d).diagonal
    (dgOdotTargetContractedFunctor R d) (dgOdotQuotientInput R d).point

end SerrePositivity.KST.SConstruction
