module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornFiniteRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornCanonicalFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTetrahedronInitialDiagonal

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

/-- 各実図式二単体ホーンの対角辺 04 は、同じ共通閉分母の実辺。 -/
lemma dgVerdierTriangleInitialDiagonal_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornCanonicalFace
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) 1 (by decide))) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D C.denominator.obj.hom).edge := by
  let a := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H
  have ht : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornCanonicalFace F 1 (by decide) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a (H 0).simplex.val) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornCanonicalFace_eq F 1 (by decide)).trans
      ((SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) 1 (by decide)) F).symm.trans
        (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn_face_cone A D C σ H 0)))
  have hA : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1 (H 0).simplex) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x C.denominator :=
    (congrArg (fun s : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋1⦌ =>
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1 s) (H 0).d₁).trans
        (C.leg (K.δ 0 (K.δ 0 σ))).src_eq
  exact (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t)) ht).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_initialDiagonal a (H 0).simplex.val).trans
      ((congrArg (fun v => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a v).edge) (congrArg Subtype.val hA)).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D C.denominator.obj.hom)))

/-- 実図式二単体ホーンの回収始対象は、元の同じ共通閉分母の始対象。 -/
lemma dgVerdierTriangleHorn_source :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0 =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left :=
  congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 => t.obj 0) (dgVerdierTriangleInitialDiagonal_edge A D C σ H)

/-- 実図式二単体ホーンの回収終対象は、元の指定終対象 x。 -/
lemma dgVerdierTriangleHorn_target :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 4 = x :=
  congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 => t.obj 1) (dgVerdierTriangleInitialDiagonal_edge A D C σ H)

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 同じ頂点錐の実二単体有限族には、一つの追加閉分母後に全残差原始元が存在する。 -/
theorem dgVerdierTrianglesResidualRefinement_nonempty {m : ℕ} (τ : Fin m → K _⦋2⦌)
    (G : ∀ j, ∀ i : Fin 3, Truncated.Edge.CompStruct
      (C.leg (K.δ 1 (K.δ i (τ j))))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i (τ j))).map ((truncation 2).map f))
      (C.leg (K.δ 0 (K.δ i (τ j))))) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornFiniteRefinement P
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left)
      (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C (τ j) (G j))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFiniteRefinement_nonempty P _ _
    (fun j => dgVerdierTriangleHorn_source A D C (τ j) (G j))
    (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleLastClosed_mem A D C (τ j) (G j))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
