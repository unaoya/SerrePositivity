module
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberComparisonProjection
public import SerrePositivity.InfinityCategories.Derived.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Derived.ComplexEdgeCalculus
public import SerrePositivity.InfinityCategories.Derived.FullCofiberSquare
public import SerrePositivity.InfinityCategories.Derived.StableColimits

/-! # 標準 cofiber 正方形の引き戻し性

概要：標準 cofiber 正方形は全複体の dg nerve で引き戻しであり、充満部分 dg 圏にも反映する。
方針：明示的比較のホモトピー同値性を slice の比較辺の可逆性に移し、標準 fiber の極限性を移送する。
規約：安定性を前提に使わない。使われ方：D7 の fiber/cofiber の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
open scoped Simplicial
variable {S : Type u} [CommRing S]

/-- 複体間のホモトピー同値を表す dg nerve の辺は可逆。 -/
lemma complex_edge_invertible_of_homotopyEquivalence
    {x y : (dgNerve S (Complex S)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := twoTruncation S (Complex S)) x y)
    (he : HomologicalComplex.homotopyEquivalences (ModuleCat.{u} S) (.up ℤ)
      (edgeChainMap e)) : IsInvertibleEdge e := by
  have hi := (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences _).mpr he
  rw [edgeChainMap_quotient] at hi
  have : IsIso ((toH0 S (Complex S)).map (SSet.Truncated.HomotopyCategory₂.homMk e)) :=
    isIso_of_reflects_iso _ (complexHomotopyComparison S)
  have : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) :=
    isIso_of_reflects_iso _ (toH0 S (Complex S))
  change IsIso ((edgeToPathHomotopyCategory _).map
    (SSet.Truncated.HomotopyCategory₂.homMk e))
  infer_instance

variable {A B C : Complex S}

/-- 標準 cofiber から標準 fiber への実際の slice 比較辺は可逆。 -/
lemma cofiberFiberComparisonSliceEdge_invertible (f : A ⟶ B) (g : A ⟶ C) :
    IsInvertibleEdge (X := sliceOver (pullbackCospan (standardFiberSquare
      (pushoutInclusionB f g) (pushoutInclusionC f g))))
      (cofiberFiberComparisonSliceEdge f g) := by
  have he : IsInvertibleEdge (X := dgNerve S (Complex S))
      (complexEdge (cofiberFiberLift f g)).toTruncated := by
    apply complex_edge_invertible_of_homotopyEquivalence
    rw [derived_edgeChainMap_complexEdge]
    exact cofiberFiberLift_homotopyEquivalence f g
  have hp := (isInvertibleEdge_congr (X := dgNerve S (Complex S))
    (cofiberFiberComparisonSliceEdge_projection f g)).mpr he
  exact derived_rightFibration_reflects_invertibleEdge
    (sliceOverProjection (pullbackCospan (standardFiberSquare
      (pushoutInclusionB f g) (pushoutInclusionC f g)))) (cofiberFiberComparisonSliceEdge f g) hp

/-- 標準 cofiber 正方形は複体の dg nerve の引き戻しでもある。 -/
lemma standardCofiberSquare_isPullback (f : A ⟶ B) (g : A ⟶ C) :
    IsPullbackSquare (standardCofiberSquare f g) := by
  have := cofiberFiberComparisonSliceEdge_invertible f g
  have hc : IsLimitCone (cofiberFiberSourceCone f g) :=
    (standardFiberCone_isLimit (pushoutInclusionB f g) (pushoutInclusionC f g)).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk (cofiberFiberComparisonSliceEdge f g))).symm
  exact rebaseCone_isLimit (cofiberFiberComparison_cospan f g).symm
    (cofiberFiberSourceCone f g) hc

/-- 標準 cofiber の四頂点が充満 dg 部分圏に属せば、そこで引き戻しでもある。 -/
lemma fullCofiberSquare_isPullback (P : Complex S → Prop) (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (pushoutCofiber f g)) :
    IsPullbackSquare (fullCofiberSquare P f g hA hB hC hP) := by
  apply isPullbackSquare_of_fullInclusion S (Complex S) P
  rw [fullCofiberSquare_inclusion]
  exact standardCofiberSquare_isPullback f g

/-- Semifree 内の標準 cofiber 正方形は ∞ 引き戻しでもある。 -/
lemma semifreeCofiberSquare_isPullback (f : A ⟶ B) (g : A ⟶ C)
    (hA : complexSemifree S A) (hB : complexSemifree S B) (hC : complexSemifree S C) :
    IsPullbackSquare (semifreeCofiberSquare f g hA hB hC) :=
  fullCofiberSquare_isPullback (complexSemifree S) f g hA hB hC
    (complexSemifree_pushoutCofiber f g hA hB hC)

/-- 任意の D(S) の span から作った標準 cofiber 押し出しは引き戻しでもある。 -/
lemma derivedSpanCofiberSquare_isPullback
    (p : (SSet.horn 2 0 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    IsPullbackSquare (derivedSpanCofiberSquare p) :=
  semifreeCofiberSquare_isPullback _ _ _ _ _

end SerrePositivity.InfinityCategories
