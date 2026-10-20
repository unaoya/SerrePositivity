module

public import SerrePositivity.InfinityCategories.F2.CoherentTransformationPointedTriangleFaces
public import SerrePositivity.InfinityCategories.F2.PrismExtensionComparisonRestriction

/-!
概要：元の全 pointed 三角形の長辺と普遍 prism の指定比較を各 fiber へ制限する。
方針：同じ始点付き延長空間に二つの実 prism を置き、終点相対空間の制限式を使う。
規約：元の長辺を再選択しない。使われ方：各点の錐と全空間比較の指定 path の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}}
  (F G J : B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y)
local notation "A" => leftUnstraightening F
local notation "w" => unstraighteningMappingFamilyWitness F J (SSet.const T.diagonal)
local notation "l" => unstraighteningMappingTriangleLongWitness F G J
  (SSet.const x) (SSet.const y) (SSet.const T.diagonal)
    T.diagram T.first T.second T.long
local notation "d" => ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ Δ[0]) ≫
  functorParameterizedPrism (intervalMappingUncurry (SSet.const T.diagonal))
local notation "v" => fst A Δ[0] ≫ pullback.fst pointedSpaceProjection F

/-- 元の長辺の二 prism が共有する底と初期値の厳密な条件。 -/
lemma coherentTriangleExtension_initial :
    v ≫ pointedSpaceProjection = (prismEndpoint 0 A ▷ (Δ[0] : SSet.{u + 1})) ≫ d := by
  rw [← (w).source, Category.assoc, (w).projection]

/-- 普遍 prism と元の全三角形の長辺を同じ延長空間の頂点として保持する。 -/
def coherentTriangleExtensionVertex (useTriangle : Bool) :
    (relativeFunctorExtensionSpace pointedSpaceProjection d
      (prismEndpoint 0 A ▷ (Δ[0] : SSet.{u + 1})) v
      (coherentTriangleExtension_initial F G J x y T)) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv _ _ _ _ _
    (if useTriangle then ⟨(l).prism, (l).projection, (l).source⟩
     else ⟨(w).prism, (w).projection, (w).source⟩)

/-- 長辺を fiber へ制限すると、元の pointed 三角形の同じ長辺そのものになる。 -/
lemma coherentTransformationPointedTriangle_long (b : B _⦋0⦌) :
    (stdSimplex.δ (1 : Fin 3) ▷ vertexFiber (leftUnstraighteningProjection F) b) ≫
        coherentTransformationPointedTriangle F G J x y T b =
      prismParameterRestriction
        (lift (vertexFiberι (leftUnstraighteningProjection F) b)
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ (l).prism := by
  rfl

set_option maxHeartbeats 800000 in
-- 同じ始点付き二重 fiber の頂点と終点相対空間の型を照合するため。
/-- 元の長辺と普遍 prism の指定終点比較は、fiber 制限後の指定比較に等しい。 -/
lemma coherentTriangleExtensionComparison_restrict (b : B _⦋0⦌) :
    let s := lift (vertexFiberι (leftUnstraighteningProjection F) b)
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    let hv := coherentTriangleExtension_initial F G J x y T
    let a := coherentTriangleExtensionVertex F G J x y T false
    let c := coherentTriangleExtensionVertex F G J x y T true
    VertexIso.map
      (VertexIso.map
        ((relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection d
          (prismEndpoint 0 A ▷ (Δ[0] : SSet.{u + 1}))
          (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne A) Δ[0])
          v hv).vertexIso a c)
        (prismExtensionEndpoint pointedSpaceProjection d v hv))
      (relativeFunctorPre pointedSpaceProjection
        ((prismEndpoint 1 A ▷ (Δ[0] : SSet.{u + 1})) ≫ d) s) =
      VertexIso.map
        ((relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection
          (prismParameterRestriction s ≫ d) (prismEndpoint 0 _)
          (prismEndpoint_zero_leftAnodyne _) (s ≫ v)
          (by rw [Category.assoc, hv]; rfl)).vertexIso
            ((prismExtensionRestriction pointedSpaceProjection d v hv s).app _ a)
            ((prismExtensionRestriction pointedSpaceProjection d v hv s).app _ c))
        (relativeFunctorExtensionSpaceι pointedSpaceProjection (prismParameterRestriction s ≫ d)
          (prismEndpoint 0 _) (s ≫ v) (by rw [Category.assoc, hv]; rfl) ≫
            relativeFunctorPre pointedSpaceProjection (prismParameterRestriction s ≫ d)
              (prismEndpoint 1 _)) :=
  prismExtensionComparison_restrict pointedSpaceProjection d v
    (coherentTriangleExtension_initial F G J x y T) _
    (coherentTriangleExtensionVertex F G J x y T false)
    (coherentTriangleExtensionVertex F G J x y T true)

end SerrePositivity.InfinityCategories.F2
