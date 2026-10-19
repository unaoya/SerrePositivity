module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornFiniteRefinement
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornCanonicalFaces
public import SerrePositivity.InfinityCategories.Derived.RoofTetrahedronInitialDiagonal

/-! # 実二単体族の共通始対象と一つの追加閉分母による同時残差消去

概要：同じ頂点錐から作る全四次ホーンの始対象を元の共通閉分母の始対象へ厳密に揃える。
方針：指定一面の始点対角辺を元の分母辺と照合し、有限原始元定理へ渡す。
規約：全ホーン充填の存在はまだ主張しない。使われ方：高次有限図式の同時細分。
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

/-- 各実図式二単体ホーンの対角辺 04 は、同じ共通閉分母の実辺。 -/
lemma dgVerdierTriangleInitialDiagonal_edge :
    (dgNerve A D).δ 1 ((dgNerve A D).δ 1 (dgFourLastHornCanonicalFace
      (dgVerdierDiagramTriangleHorn A D C σ H) 1 (by decide))) =
      (dgClosedEdge A D C.denominator.obj.hom).edge := by
  let a := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let F := dgVerdierDiagramTriangleHorn A D C σ H
  have ht : dgFourLastHornCanonicalFace F 1 (by decide) =
      SSet.yonedaEquiv (roofPointSliceTetrahedron a (H 0).simplex.val) :=
    (dgFourLastHornCanonicalFace_eq F 1 (by decide)).trans
      ((SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) 1 (by decide)) F).symm.trans
        (congrArg (SSet.yonedaEquiv (X := dgNerve A D))
          (dgVerdierDiagramTriangleHorn_face_cone A D C σ H 0)))
  have hA : (dgVerdierOver A D P x : SSet).δ 1
      ((dgVerdierOver A D P x : SSet).δ 1 (H 0).simplex) =
      dgClosedVerdierDenominatorVertex A D P x C.denominator :=
    (congrArg (fun s : (dgVerdierOver A D P x : SSet) _⦋1⦌ =>
      (dgVerdierOver A D P x : SSet).δ 1 s) (H 0).d₁).trans
        (C.leg (K.δ 0 (K.δ 0 σ))).src_eq
  exact (congrArg (fun t : Simplex A D 3 => (dgNerve A D).δ 1 ((dgNerve A D).δ 1 t)) ht).trans
    ((roofPointSliceTetrahedron_initialDiagonal a (H 0).simplex.val).trans
      ((congrArg (fun v => (roofPointSliceVertexEdge a v).edge) (congrArg Subtype.val hA)).trans
        (dgClosedOverVertex_edge A D C.denominator.obj.hom)))

/-- 実図式二単体ホーンの回収始対象は、元の同じ共通閉分母の始対象。 -/
lemma dgVerdierTriangleHorn_source :
    (HornData.knownData (dgVerdierDiagramTriangleHorn A D C σ H)).obj 0 =
      ForgetEnrichment.to (Complex A) C.denominator.obj.left :=
  congrArg (fun t : Simplex A D 1 => t.obj 0) (dgVerdierTriangleInitialDiagonal_edge A D C σ H)

/-- 実図式二単体ホーンの回収終対象は、元の指定終対象 x。 -/
lemma dgVerdierTriangleHorn_target :
    (HornData.knownData (dgVerdierDiagramTriangleHorn A D C σ H)).obj 4 = x :=
  congrArg (fun t : Simplex A D 1 => t.obj 1) (dgVerdierTriangleInitialDiagonal_edge A D C σ H)

variable [Small.{u} D] [IsDGPretriangulated A D]

/-- 同じ頂点錐の実二単体有限族には、一つの追加閉分母後に全残差原始元が存在する。 -/
theorem dgVerdierTrianglesResidualRefinement_nonempty {m : ℕ} (τ : Fin m → K _⦋2⦌)
    (G : ∀ j, ∀ i : Fin 3, Truncated.Edge.CompStruct
      (C.leg (K.δ 1 (K.δ i (τ j))))
      ((edgeOfSimplex (K.δ i (τ j))).map ((truncation 2).map f))
      (C.leg (K.δ 0 (K.δ i (τ j))))) :
    Nonempty (DGFourLastHornFiniteRefinement P
      (ForgetEnrichment.to (Complex A) C.denominator.obj.left)
      (fun j => dgVerdierDiagramTriangleHorn A D C (τ j) (G j))) :=
  dgFourLastHornFiniteRefinement_nonempty P _ _
    (fun j => dgVerdierTriangleHorn_source A D C (τ j) (G j))
    (fun j => dgVerdierDiagramTriangleLastClosed_mem A D C (τ j) (G j))

end SerrePositivity.InfinityCategories
