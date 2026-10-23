module

public import SerrePositivity.InfinityCategories.F1.Transport.TensorFiber
public import SerrePositivity.InfinityCategories.F1.Transport.SquareRepresentation
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFamilyVertices
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorSpaceCurrying

/-!
概要：積上の四角形をパラメーターの頂点で評価する。
方針：固定パラメーターの挿入と内部 currying の頂点評価を比較する。
規約：四角形の二つの射をともに保持する。
使われ方：表現空間の積と内部 Hom の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：積上の四角形を一つのパラメーター頂点で制限する。
方針：底と全空間に同じ頂点を挿入する。
規約：分類図式と全空間の射を同時に評価する。
使われ方：各パラメーターでの表現条件の検査。 -/
def LeftTransportSquare.tensorAt {E B K : SSet.{u + 1}} {p : E ⟶ B}
    (S : LeftTransportSquare (p ▷ K)) (k : K _⦋0⦌) : LeftTransportSquare p :=
  ⟨lift (𝟙 B) (SSet.const k) ≫ S.diagram,
    lift (𝟙 E) (SSet.const k) ≫ S.pointedMap, by
      rw [Category.assoc, S.comm, ← Category.assoc]
      have h : lift (𝟙 E) (SSet.const k) ≫ (p ▷ K) = p ≫ lift (𝟙 B) (SSet.const k) := by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc, whiskerRight_fst, lift_fst]
          rw [← Category.assoc, lift_fst, Category.id_comp, Category.comp_id]
        · simp only [Category.assoc, whiskerRight_snd, lift_snd, SSet.comp_const]
      rw [h, Category.assoc]⟩

/-- 概要：内部 currying の頂点評価は元の射への固定パラメーター挿入。
方針：内部 Hom の自然変換を全次数で評価する。
規約：任意の単体集合と頂点。
使われ方：積上の四角形の currying の頂点公式。 -/
lemma transportIhomCurry_vertex_at {A K X : SSet.{u}} (F : A ⊗ K ⟶ X)
    (k : K _⦋0⦌) :
    (evaluateFunctorAt k).app (Opposite.op ⦋0⦌)
        ((ihomCurryIso A K X).hom.app _ (functorVertex F)) =
      functorVertex (lift (𝟙 A) (SSet.const k) ≫ F) := by
  change (evaluateFunctorAt k).app _
    ((functorSpaceCurryMap A K X).app _ (functorVertex F)) = _
  rw [functorSpaceCurryMap_vertex, evaluateFunctorAt_functorVertex]
  have h := uncurry_at_vertex (curry F) k
  rw [uncurry_curry] at h
  exact ((congrArg (functorVertexEquiv A X) h).trans
    ((functorVertexEquiv A X).apply_symm_apply _)).symm

/-- 概要：四角形の currying を頂点で評価すると実際の固定パラメーターの四角形。
方針：同型の両射影を評価し、内部 currying の頂点公式を使う。
規約：厳密な頂点の一致。
使われ方：全部分複体の頂点条件の比較。 -/
lemma transportSquareTensorIso_vertex_at {E B K : SSet.{u + 1}} {p : E ⟶ B}
    (S : LeftTransportSquare (p ▷ K)) (k : K _⦋0⦌) :
    (evaluateFunctorAt k).app (Opposite.op ⦋0⦌)
        ((transportSquareTensorIso p K).hom.app _ (transportSquareVertex S)) =
      transportSquareVertex (S.tensorAt k) := by
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback ((ihom E).map pointedSpaceProjection)
      ((pre p).app SpaceInfinity)).app (Opposite.op ⦋0⦌))
  · change ((ihom K).map (transportSquarePointed p) ≫ evaluateFunctorAt k).app _
        ((transportSquareTensorIso p K).hom.app _ (transportSquareVertex S)) = _
    have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (transportSquareVertex S))
      (transportSquareTensorIso_hom_pointed p K)
    change ((ihom K).map (transportSquarePointed p)).app _
        ((transportSquareTensorIso p K).hom.app _ (transportSquareVertex S)) = _ at h
    change (evaluateFunctorAt k).app _
        (((ihom K).map (transportSquarePointed p)).app _
          ((transportSquareTensorIso p K).hom.app _ (transportSquareVertex S))) = _
    rw [h]
    change (evaluateFunctorAt k).app _
        ((ihomCurryIso E K PointedSpaceInfinity).hom.app _
          ((transportSquarePointed (p ▷ K)).app _ (transportSquareVertex S))) = _
    rw [transportSquareVertex_pointed, transportIhomCurry_vertex_at]
    exact (transportSquareVertex_pointed (S.tensorAt k)).symm
  · change ((ihom K).map (transportSquareDiagram p) ≫ evaluateFunctorAt k).app _
        ((transportSquareTensorIso p K).hom.app _ (transportSquareVertex S)) = _
    have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (transportSquareVertex S))
      (transportSquareTensorIso_hom_diagram p K)
    change ((ihom K).map (transportSquareDiagram p)).app _
        ((transportSquareTensorIso p K).hom.app _ (transportSquareVertex S)) = _ at h
    change (evaluateFunctorAt k).app _
        (((ihom K).map (transportSquareDiagram p)).app _
          ((transportSquareTensorIso p K).hom.app _ (transportSquareVertex S))) = _
    rw [h]
    change (evaluateFunctorAt k).app _
        ((ihomCurryIso B K SpaceInfinity).hom.app _
          ((transportSquareDiagram (p ▷ K)).app _ (transportSquareVertex S))) = _
    rw [transportSquareVertex_diagram, transportIhomCurry_vertex_at]
    exact (transportSquareVertex_diagram (S.tensorAt k)).symm

end SerrePositivity.InfinityCategories
