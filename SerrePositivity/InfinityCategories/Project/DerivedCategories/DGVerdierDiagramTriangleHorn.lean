module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteLegCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofSliceFourHorn

/-! # 実分母図式の二単体に沿う四次整合性ホーン

概要：元の実図式二単体と、その三辺に同じ頂点脚で与えた辺錐を指定四面へ束ねる。
方針：実 over 内の六つの共通辺の厳密一致を、元の dg nerve の四次外ホーンへ移す。
規約：最後の面の充填可能性は主張しない。使われ方：追加分母後の高次整合性の残差計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))

/-- 三つの辺錐と元の二単体は、実 over 内の三次境界を指定する。 -/
def dgVerdierDiagramTriangleBoundary : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ThreeSimplexFaceBoundary
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.diagramTriangleConeBoundary (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι) σ
    (fun v => (C.leg v).edge.val) (fun i => (H i).simplex.val)
    (fun i => congrArg Subtype.val (H i).d₀)
    (fun i => congrArg Subtype.val (H i).d₁)
    (fun i => congrArg Subtype.val (H i).d₂)

/-- 指定図式二単体と同じ頂点脚の三つの辺錐に対する、元の dg nerve の四次ホーン。 -/
def dgVerdierDiagramTriangleHorn : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHorn _ (dgVerdierDiagramTriangleBoundary A D C σ H)

omit [Small.{u} D] in
/-- 四次ホーンの零面は、元の指定実図式二単体の回収四面体。 -/
lemma dgVerdierDiagramTriangleHorn_face0 :
    horn.ι (4 : Fin 5) 0 (by decide) ≫ dgVerdierDiagramTriangleHorn A D C σ H =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ (f.app _ σ).val :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHorn_face _ (dgVerdierDiagramTriangleBoundary A D C σ H) 0

omit [Small.{u} D] in
/-- 四次ホーンの残る指定三面は、同じ三つの実辺錐の回収四面体。 -/
lemma dgVerdierDiagramTriangleHorn_face_cone (i : Fin 3) :
    horn.ι (4 : Fin 5) i.succ.castSucc (Fin.castSucc_ne_last _) ≫
      dgVerdierDiagramTriangleHorn A D C σ H =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ (H i).simplex.val := by
  fin_cases i
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHorn_face _ (dgVerdierDiagramTriangleBoundary A D C σ H) 1
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHorn_face _ (dgVerdierDiagramTriangleBoundary A D C σ H) 2
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceFourHorn_face _ (dgVerdierDiagramTriangleBoundary A D C σ H) 3

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 三つの図式辺の同時細分から、同じ頂点脚を持つ実四次ホーンを直接供給する。 -/
def dgVerdierDiagramRefinedTriangleHorn
    (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement A D C (fun i : Fin 3 => K.δ i σ)) :
    (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  dgVerdierDiagramTriangleHorn A D T.vertexCone σ
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.vertexConeCompStruct A D T i)

/-- 三辺の同時細分から供給したホーンも、元の実図式二単体を零面に保つ。 -/
lemma dgVerdierDiagramRefinedTriangleHorn_face0
    (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement A D C (fun i : Fin 3 => K.δ i σ)) :
    horn.ι (4 : Fin 5) 0 (by decide) ≫ dgVerdierDiagramRefinedTriangleHorn A D C σ T =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ (f.app _ σ).val :=
  dgVerdierDiagramTriangleHorn_face0 A D T.vertexCone σ
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.vertexConeCompStruct A D T i)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
