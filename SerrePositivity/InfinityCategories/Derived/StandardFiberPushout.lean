module
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberComparisonProjection
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberPullback
public import SerrePositivity.InfinityCategories.Derived.PushoutComparison

/-! # 標準 fiber 正方形の押し出し性

概要：標準 fiber 正方形は全複体の dg nerve と Semifree の内部で押し出しでもある。
方針：明示的比較のホモトピー同値性を coslice に反映し、標準 cofiber の余極限性を移す。
規約：安定性は仮定しない。使われ方：D7 の fiber/cofiber の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
open scoped Simplicial
variable {S : Type u} [CommRing S] {B C D : Complex S}

/-- 標準 cofiber から元の fiber 余錐への実際の coslice 比較辺は可逆。 -/
lemma fiberCofiberComparisonSliceEdge_invertible (g : B ⟶ D) (h : C ⟶ D) :
    IsInvertibleEdge (X := sliceUnder (pushoutSpan (standardCofiberSquare
      (pullbackProjectionB g h) (pullbackProjectionC g h))))
      (fiberCofiberComparisonSliceEdge g h) := by
  have he : IsInvertibleEdge (X := dgNerve S (Complex S))
      (complexEdge (fiberCofiberDesc g h)).toTruncated := by
    apply complex_edge_invertible_of_homotopyEquivalence
    rw [derived_edgeChainMap_complexEdge]
    exact fiberCofiberDesc_homotopyEquivalence g h
  have hp := (isInvertibleEdge_congr (X := dgNerve S (Complex S))
    (fiberCofiberComparisonSliceEdge_projection g h)).mpr he
  exact leftFibration_reflects_invertibleEdge
    (sliceUnderProjection (pushoutSpan (standardCofiberSquare
      (pullbackProjectionB g h) (pullbackProjectionC g h))))
    (fiberCofiberComparisonSliceEdge g h) hp

/-- 標準 fiber 正方形は複体の dg nerve の押し出しでもある。 -/
lemma standardFiberSquare_isPushout (g : B ⟶ D) (h : C ⟶ D) :
    IsPushoutSquare (standardFiberSquare g h) := by
  have := fiberCofiberComparisonSliceEdge_invertible g h
  have hc : IsColimitCone (fiberCofiberTargetCocone g h) :=
    (standardCofiberCocone_isColimit (pullbackProjectionB g h)
      (pullbackProjectionC g h)).of_vertexIso
        (asIso (SSet.Truncated.HomotopyCategory.homMk (fiberCofiberComparisonSliceEdge g h)))
  exact (rebaseCocone_isColimit_iff (fiberCofiberComparison_span g h)
    (pushoutCocone (standardFiberSquare g h))).mp hc

/-- 標準 fiber の四頂点が充満 dg 部分圏に属せば、そこで押し出しでもある。 -/
lemma fullFiberSquare_isPushout (P : Complex S → Prop) (g : B ⟶ D) (h : C ⟶ D)
    (hB : P B) (hC : P C) (hD : P D) (hP : P (pullbackFiber g h)) :
    IsPushoutSquare (fullFiberSquare P g h hB hC hD hP) := by
  apply isPushoutSquare_of_fullInclusion P
  rw [fullFiberSquare_inclusion]
  exact standardFiberSquare_isPushout g h

/-- Semifree 内の標準 fiber 正方形は押し出しでもある。 -/
lemma semifreeFiberSquare_isPushout (g : B ⟶ D) (h : C ⟶ D)
    (hB : complexSemifree S B) (hC : complexSemifree S C) (hD : complexSemifree S D) :
    IsPushoutSquare (semifreeFiberSquare g h hB hC hD) :=
  fullFiberSquare_isPushout (complexSemifree S) g h hB hC hD
    (complexSemifree_biprodFiber S (fiberDifference g h) hB hC hD)

/-- 任意の D(S) の cospan から作った標準 fiber 引き戻しは押し出しでもある。 -/
lemma derivedCospanFiberSquare_isPushout
    (p : (SSet.horn 2 2 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    IsPushoutSquare (derivedCospanFiberSquare p) :=
  semifreeFiberSquare_isPushout _ _ _ _ _

end SerrePositivity.InfinityCategories
