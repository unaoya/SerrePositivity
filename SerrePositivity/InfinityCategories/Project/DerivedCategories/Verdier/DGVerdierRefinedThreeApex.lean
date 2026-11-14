module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierRefinedThreeFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInitialRefinementDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierTriangleCommonSource

/-! # 閉細分後の over 三単体の新 apex の実分母性

概要：回収した始頂点の構造辺は、元の共通閉分母と追加閉分母の同じ実合成。
方針：指定一面からの始点対角辺公式を使い、一般閉始点細分の合成表示へ渡す。
規約：元の指定集合 P を保つ。使われ方：実分母 over への三単体の持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))

/-- 実図式二単体ホーンの始点対角辺から回収した、元の閉分母射。 -/
def dgVerdierTriangleInitialClosed :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 4) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornCanonicalFace
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) 1 (by decide)))).edgeClosed 0 1 (by decide)

/-- 回収した対角閉射の実辺は、元の同じ共通閉分母の実辺。 -/
lemma dgVerdierTriangleInitialClosed_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (dgVerdierTriangleInitialClosed A D C σ H)).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D C.denominator.obj.hom).edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexEdge_closed_normal A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornCanonicalFace
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) 1 (by decide))))).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTriangleInitialDiagonal_edge A D C σ H)

variable (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
variable (F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 回収 over 三単体の新始頂点の辺は、指定細分一面の始点対角辺。 -/
lemma dgVerdierDiagramRefinedThreeApex_edge
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF))))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s)) := by
  have h₁ := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex_face1 A D C σ H q s F hF)
  rw [Equiv.apply_symm_apply] at h₁
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_initialDiagonal _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF))).symm.trans
      (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t)) h₁)

/-- 新始頂点の辺は、追加閉分母と元の指定対角閉射の実合成。 -/
lemma dgVerdierDiagramRefinedThreeApex_comp
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF))))).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (s ≫ dgVerdierTriangleInitialClosed A D C σ H)).edge :=
  (dgVerdierDiagramRefinedThreeApex_edge A D C σ H q s F hF).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronInitialRefinement_initialDiagonal A D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornCanonicalFace (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) 1 (by decide)) q s)

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 一つの追加実閉分母の後の新始頂点も、元の実 Verdier 分母条件を満たす。 -/
lemma dgVerdierDiagramRefinedThreeApex_mem
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))).δ 1
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF)))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex
  rw [dgVerdierDiagramRefinedThreeApex_comp]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P s (dgVerdierTriangleInitialClosed A D C σ H) hs
  rw [dgVerdierTriangleInitialClosed_edge]
  exact C.denominator.property

end SerrePositivity.InfinityCategories.Project.DerivedCategories
