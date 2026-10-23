module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleExtensionRestriction

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
/-- 実延長を制限した頂点の内部 Hom 成分は、同じ実延長の前合成。 -/
lemma prismExtensionRestriction_vertex_value {A C E B K : SSet.{u}}
    (p : E ⟶ B) (d : ((Δ[1] : SSet.{u}) ⊗ A) ⊗ K ⟶ B)
    (v : A ⊗ K ⟶ E) (hv : v ≫ p = (prismEndpoint 0 A ▷ K) ≫ d)
    (s : C ⟶ A ⊗ K) (W : (Δ[1] ⊗ A) ⊗ K ⟶ E)
    (hW : W ≫ p = d) (hW₀ : (prismEndpoint 0 A ▷ K) ≫ W = v) :
    (((prismExtensionRestriction p d v hv s).app (Opposite.op ⦋0⦌)
      (relativeFunctorExtensionSpaceVertexEquiv p d (prismEndpoint 0 A ▷ K) v hv
        ⟨W, hW, hW₀⟩)).val).val = functorVertex (prismParameterRestriction s ≫ W) := by
  exact congrArg (fun z => z.val.val)
    (relativeExtensionRestriction_vertex p d (prismEndpoint 0 A ▷ K) v hv
      (prismParameterRestriction s) s (prismEndpoint 0 C) rfl W hW hW₀)

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

set_option maxHeartbeats 800000 in
-- 二重 fiber の包含から、元の全三角形の長辺の関手頂点への型照合に必要。
/-- 制限後の比較の第二入力は、元の全 pointed 三角形の同じ長辺を表す。 -/
lemma coherentTriangleExtensionRestriction_long (b : B _⦋0⦌) :
    let s := lift (vertexFiberι (leftUnstraighteningProjection F) b)
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    let hv := coherentTriangleExtension_initial F G J x y T
    (((prismExtensionRestriction pointedSpaceProjection d v hv s).app (Opposite.op ⦋0⦌)
      (coherentTriangleExtensionVertex F G J x y T true)).val).val =
        functorVertex
          ((stdSimplex.δ (1 : Fin 3) ▷ vertexFiber (leftUnstraighteningProjection F) b) ≫
            coherentTransformationPointedTriangle F G J x y T b) := by
  dsimp only
  change (((prismExtensionRestriction pointedSpaceProjection d v
    (coherentTriangleExtension_initial F G J x y T) _).app (Opposite.op ⦋0⦌)
      (relativeFunctorExtensionSpaceVertexEquiv _ _ _ _ _
        ⟨(l).prism, (l).projection, (l).source⟩)).val).val = _
  rw [prismExtensionRestriction_vertex_value pointedSpaceProjection d v
    (coherentTriangleExtension_initial F G J x y T) _ (l).prism (l).projection (l).source]
  exact congrArg functorVertex
    (coherentTransformationPointedTriangle_long F G J x y T b).symm

end SerrePositivity.InfinityCategories.F2
