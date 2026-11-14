module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofRefinements
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientRoofComparison

/-! # 商内の実屋根図式の全細分は実ホモトピー同値

概要：厳密屋根の元の閉細分射は商で可逆になり、実 pinched 屋根図式の写像は同値。
方針：実 over の二対三性、商による分母の反転、閉前合成の全 Hom 準同型を接続する。
規約：屋根図式の余極限や局所化の普遍性は別途必要。使われ方：実屋根の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 元の任意の指定閉分母は、商の指定実閉辺として可逆。 -/
lemma dgQuotientClosedDenominator_isInvertible (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {q x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (s : q ⟶ x)
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (QuotientObject D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (QuotientObject D P) ((inclusion A D P).onClosed.map s)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_invertsVerdierEdges A D P hP hs
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map A D (inclusion A D P) s)).mp h

/-- 厳密屋根の指定閉細分射は、商の指定実閉辺として可逆。 -/
lemma dgQuotientRoofRefinement_isInvertible (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (QuotientObject D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (QuotientObject D P) ((inclusion A D P).onClosed.map r.hom.left)) := by
  exact dgQuotientClosedDenominator_isInvertible A D P hP r.hom.left
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinement_mem A D P x r)

/-- 商側の実 pinched 屋根図式の全ての指定細分写像は実ホモトピー同値。 -/
lemma dgQuotientRoofDiagram_map_equivalence (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x y : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofDiagram A D P x y).map r.op) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
      (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) t.obj.left))
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map r.hom.left))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition_equivalence_of_invertible A (QuotientObject D P) _
    (dgQuotientRoofRefinement_isInvertible A D P hP x r)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
