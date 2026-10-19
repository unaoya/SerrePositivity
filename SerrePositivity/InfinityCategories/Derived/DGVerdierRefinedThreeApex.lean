module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRefinedThreeFaces
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementDiagonal
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTriangleCommonSource

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))

/-- 実図式二単体ホーンの始点対角辺から回収した、元の閉分母射。 -/
def dgVerdierTriangleInitialClosed :
    ForgetEnrichment.of (Complex A)
      ((HornData.knownData (dgVerdierDiagramTriangleHorn A D C σ H)).obj 0) ⟶
    ForgetEnrichment.of (Complex A)
      ((HornData.knownData (dgVerdierDiagramTriangleHorn A D C σ H)).obj 4) :=
  ((dgNerve A D).δ 1 ((dgNerve A D).δ 1 (dgFourLastHornCanonicalFace
    (dgVerdierDiagramTriangleHorn A D C σ H) 1 (by decide)))).edgeClosed 0 1 (by decide)

/-- 回収した対角閉射の実辺は、元の同じ共通閉分母の実辺。 -/
lemma dgVerdierTriangleInitialClosed_edge :
    (dgClosedEdge A D (dgVerdierTriangleInitialClosed A D C σ H)).edge =
      (dgClosedEdge A D C.denominator.obj.hom).edge :=
  (dgSimplexEdge_closed_normal A D ((dgNerve A D).δ 1 ((dgNerve A D).δ 1
    (dgFourLastHornCanonicalFace
      (dgVerdierDiagramTriangleHorn A D C σ H) 1 (by decide))))).symm.trans
      (dgVerdierTriangleInitialDiagonal_edge A D C σ H)

variable (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  ((HornData.knownData (dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
variable (F : Δ[4] ⟶ dgNerve A D)

/-- 回収 over 三単体の新始頂点の辺は、指定細分一面の始点対角辺。 -/
lemma dgVerdierDiagramRefinedThreeApex_edge
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (roofPointSliceVertexEdge _ ((sliceOver _).δ 1 ((sliceOver _).δ 1 ((sliceOver _).δ 1
      (dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF))))).edge =
      (dgNerve A D).δ 1 ((dgNerve A D).δ 1
        (dgFourLastHornRefinedFace1 (dgVerdierDiagramTriangleHorn A D C σ H) q s)) := by
  have h₁ := congrArg (SSet.yonedaEquiv (X := dgNerve A D))
    (dgVerdierDiagramRefinedOverThreeSimplex_face1 A D C σ H q s F hF)
  rw [Equiv.apply_symm_apply] at h₁
  exact (roofPointSliceTetrahedron_initialDiagonal _ ((sliceOver _).δ 1
    (dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF))).symm.trans
      (congrArg (fun t : Simplex A D 3 => (dgNerve A D).δ 1 ((dgNerve A D).δ 1 t)) h₁)

/-- 新始頂点の辺は、追加閉分母と元の指定対角閉射の実合成。 -/
lemma dgVerdierDiagramRefinedThreeApex_comp
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (roofPointSliceVertexEdge _ ((sliceOver _).δ 1 ((sliceOver _).δ 1 ((sliceOver _).δ 1
      (dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF))))).edge =
      (dgClosedEdge A D (s ≫ dgVerdierTriangleInitialClosed A D C σ H)).edge :=
  (dgVerdierDiagramRefinedThreeApex_edge A D C σ H q s F hF).trans
    (dgTetrahedronInitialRefinement_initialDiagonal A D
      (dgFourLastHornCanonicalFace (dgVerdierDiagramTriangleHorn A D C σ H) 1 (by decide)) q s)

variable [Small.{u} D] [IsDGPretriangulated A D]

/-- 一つの追加実閉分母の後の新始頂点も、元の実 Verdier 分母条件を満たす。 -/
lemma dgVerdierDiagramRefinedThreeApex_mem
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    IsDGVerdierOverVertex A D P x
      ((sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))).δ 1
        ((sliceOver _).δ 1 ((sliceOver _).δ 1
          (dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF)))) := by
  unfold IsDGVerdierOverVertex
  rw [dgVerdierDiagramRefinedThreeApex_comp]
  apply dgClosedVerdierDenominator_comp A D P s (dgVerdierTriangleInitialClosed A D C σ H) hs
  rw [dgVerdierTriangleInitialClosed_edge]
  exact C.denominator.property

end SerrePositivity.InfinityCategories
