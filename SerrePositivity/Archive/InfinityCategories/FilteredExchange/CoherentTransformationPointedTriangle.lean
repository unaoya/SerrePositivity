module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedTriangleFiberRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationVertexTriangle
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningMappingTrianglePrism

/-!
概要：元の coherent 合成三角形の実際の pointed な全持ち上げを各 fiber へ制限する。
方針：元の二辺の普遍的な証拠を保つ持ち上げから長辺と各点の全三角形を取る。
規約：元の全二単体を保持。使われ方：各点の元の錐と全空間比較の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}}
  (F G J : B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y)

/-- 概要：元の合成三角形と元の二辺を保つ pointed な全三角形の持ち上げ。
方針：元の零単体パラメータの普遍証拠を固定する。
規約：元の二単体を型に含む。使われ方：比較同型の元の二次整合の証拠。 -/
def coherentTransformationTriangleLift :=
  unstraighteningMappingTrianglePrism F G J (SSet.const x) (SSet.const y)
    T.diagram T.first T.second

/-- 概要：比較に使う長辺の証拠は同じ全三角形の長辺そのもの。
方針：構成の定義を展開。規約：証拠の選び直しなし。使われ方：元の指定同型の識別。 -/
lemma coherentTransformationTriangleLift_long :
    (unstraighteningMappingTriangleLongWitness F G J (SSet.const x) (SSet.const y)
      (SSet.const T.diagonal) T.diagram T.first T.second T.long).prism =
        (α_ (Δ[1] : SSet.{u + 1}) (leftUnstraightening F) Δ[0]).hom ≫
          (stdSimplex.δ (1 : Fin 3) ▷ (leftUnstraightening F ⊗ (Δ[0] : SSet.{u + 1}))) ≫
            (coherentTransformationTriangleLift F G J x y T).prism := rfl

/-- 概要：元の全 pointed 三角形の始域 fiber での制限。
方針：元の fiber 包含と一点パラメータを代入。
規約：全二単体を保持。使われ方：各点の元の native 錐との比較。 -/
def coherentTransformationPointedTriangle (b : B _⦋0⦌) :
    (Δ[2] : SSet.{u + 1}) ⊗ vertexFiber (leftUnstraighteningProjection F) b ⟶
      PointedSpaceInfinity.{u} :=
  (Δ[2] ◁ lift (vertexFiberι (leftUnstraighteningProjection F) b)
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫
      (coherentTransformationTriangleLift F G J x y T).prism

/-- 概要：各 fiber の全 pointed 三角形の底は元の二単体の指定一点評価。
方針：保持した元の射影式を fiber へ制限。
規約：全二単体での厳密な式。使われ方：元の各点の可換性の保持。 -/
lemma coherentTransformationPointedTriangle_projection (b : B _⦋0⦌) :
    coherentTransformationPointedTriangle F G J x y T b ≫ pointedSpaceProjection =
      fst (Δ[2] : SSet.{u + 1}) (vertexFiber (leftUnstraighteningProjection F) b) ≫
        coherentTransformationPointDiagram T.diagram b :=
  pointedTriangleFiberRestriction_projection (leftUnstraighteningProjection F) b T.diagram _
    (coherentTransformationTriangleLift F G J x y T).projection

end SerrePositivity.InfinityCategories.F2
