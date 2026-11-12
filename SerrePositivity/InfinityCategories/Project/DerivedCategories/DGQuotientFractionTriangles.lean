module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRoofH0
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedMappedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyEdges

/-! # 商の実辺の分数表示と指定三辺の合成二単体

概要：局所 K-flat な商の任意の実辺は、元の実分母・実分子からの合成二単体で表示できる。
方針：実 roof の H⁰ 比較式を通常の h に反映し、同じ三辺を保って二単体を回収する。
規約：高次の境界に関する coherent 分数表示は別途必要。使われ方：β3 の写像空間の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 任意の実 roof の比較式を、指定分母像・入力辺・分子像の実合成二単体へ昇格する。 -/
lemma DGQuotientActualRoof.compositionSimplex (P : Set D) {x z : D}
    (k : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨x⟩ : QuotientObject D P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨z⟩ : QuotientObject D P)))
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientActualRoof A D P x z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientEdgeDerivedMap A D P k)) :
    Nonempty (Truncated.Edge.CompStruct
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) r.denominator) k
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) r.numerator)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (QuotientObject D P)).functor.map_injective
  rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge_closed, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge_closed]
  exact r.h0_comparison A D P k

/-- 指定 Verdier 分母の像は、像対象を端点とする実辺として可逆。 -/
lemma dgQuotientEdge_isInvertible_of_verdier [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) {x y : D}
    (s : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) (hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) s) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) s.edge).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P))) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_invertsVerdierEdges A D P hP hs
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) s.edge).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)))
    (f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) s) rfl).mp h

/-- 商の任意の実辺は、元の実分母と実分子の像を二辺とする実二単体で表せる。 -/
theorem dgQuotientEdge_exists_fractionTriangle [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) {x z : D}
    (k : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨x⟩ : QuotientObject D P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨z⟩ : QuotientObject D P))) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      (g : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z)),
      s.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) s) ∧
      Nonempty (Truncated.Edge.CompStruct
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) s) k
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (QuotientObject D P) (inclusion A D P) g)) := by
  obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotient_exists_actualRoof A D P hP x z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientEdgeDerivedMap A D P k)
  exact ⟨r.source, r.denominator, r.numerator, r.denominator_mem,
    dgQuotientEdge_isInvertible_of_verdier A D P hP r.denominator r.denominator_mem,
    r.compositionSimplex A D P k⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
