module

public import SerrePositivity.InfinityCategories.F1.TransportSquareSpace

/-!
概要：可換四角形の空間の頂点と厳密な四角形のデータの対応。
方針：二つの関手空間の頂点を射へ戻し、引き戻し条件から可換性を回収する。
規約：底の射と全空間の射を同時に保つ全単射。
使われ方：Kerodon §5.6.8、表現の条件を周囲の空間の頂点条件として課す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：可換四角形は二つの射で一意に決まる。
方針：構造の成分を同定し、可換性の証明無関係性を使う。
規約：二つの射の厳密な等式を要求する。
使われ方：Kerodon §5.6.8、四角形の制限の比較。 -/
lemma LeftTransportSquare.ext {E B : SSet.{u + 1}} {p : E ⟶ B}
    (S T : LeftTransportSquare p) (hF : S.diagram = T.diagram)
    (hφ : S.pointedMap = T.pointedMap) : S = T := by
  cases S
  cases T
  dsimp only at hF hφ
  cases hF
  cases hφ
  rfl

/-- 概要：四角形の空間の頂点から実際の可換四角形を回収する。
方針：両射影の関手頂点を通常の射へ戻す。
規約：底も全空間も quasicategory である必要はない。
使われ方：Kerodon §5.6.8、頂点条件の判定。 -/
noncomputable def transportSquareOfVertex {E B : SSet.{u + 1}} (p : E ⟶ B)
    (v : (transportSquareSpace p) _⦋0⦌) : LeftTransportSquare p := by
  let F := (functorVertexEquiv B SpaceInfinity.{u}).symm ((transportSquareDiagram p).app _ v)
  let φ := (functorVertexEquiv E PointedSpaceInfinity.{u}).symm ((transportSquarePointed p).app _ v)
  have hF : functorVertex F = (transportSquareDiagram p).app _ v :=
    (functorVertexEquiv B SpaceInfinity).apply_symm_apply _
  have hφ : functorVertex φ = (transportSquarePointed p).app _ v :=
    (functorVertexEquiv E PointedSpaceInfinity).apply_symm_apply _
  refine ⟨F, φ, ?_⟩
  apply functorVertex_injective
  change ((ihom E).map pointedSpaceProjection).app _ (functorVertex φ) =
    ((pre p).app SpaceInfinity).app _ (functorVertex F)
  rw [hF, hφ]
  exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v) (transportSquareSpace_condition p)

/-- 概要：頂点から回収した四角形を頂点へ戻すと元の頂点。
方針：引き戻しの両射影で比較し、関手頂点の往復を使う。
規約：頂点の厳密な等式。
使われ方：Kerodon §5.6.8、頂点対応の全射性。 -/
lemma transportSquareVertex_ofVertex {E B : SSet.{u + 1}} (p : E ⟶ B)
    (v : (transportSquareSpace p) _⦋0⦌) :
    transportSquareVertex (transportSquareOfVertex p v) = v := by
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback ((ihom E).map pointedSpaceProjection)
      ((pre p).app SpaceInfinity)).app (Opposite.op ⦋0⦌))
  · change (transportSquarePointed p).app _
      (transportSquareVertex (transportSquareOfVertex p v)) = _
    rw [transportSquareVertex_pointed]
    exact (functorVertexEquiv E PointedSpaceInfinity).apply_symm_apply _
  · change (transportSquareDiagram p).app _
      (transportSquareVertex (transportSquareOfVertex p v)) = _
    rw [transportSquareVertex_diagram]
    exact (functorVertexEquiv B SpaceInfinity).apply_symm_apply _

/-- 概要：可換四角形の頂点表示は単射。
方針：両射影の頂点から二つの射の等式を回収する。
規約：可換性の証明の違いはデータを変えない。
使われ方：Kerodon §5.6.8、厳密な表現データの保存。 -/
lemma transportSquareVertex_injective {E B : SSet.{u + 1}} (p : E ⟶ B) :
    Function.Injective (transportSquareVertex (p := p)) := by
  intro S T h
  have hF := congrArg ((transportSquareDiagram p).app (Opposite.op ⦋0⦌)) h
  have hφ := congrArg ((transportSquarePointed p).app (Opposite.op ⦋0⦌)) h
  rw [transportSquareVertex_diagram, transportSquareVertex_diagram] at hF
  rw [transportSquareVertex_pointed, transportSquareVertex_pointed] at hφ
  have hF' := functorVertex_injective hF
  have hφ' := functorVertex_injective hφ
  cases S
  cases T
  dsimp only at hF' hφ'
  cases hF'
  cases hφ'
  rfl

/-- 概要：可換四角形のデータと周囲の関手空間の頂点の全単射。
方針：構成した頂点表示と回収を往復する。
規約：厳密な可換四角形全体についての対応。
使われ方：Kerodon §5.6.8、transport witnesses の頂点の同定。 -/
noncomputable def transportSquareVertexEquiv {E B : SSet.{u + 1}} (p : E ⟶ B) :
    LeftTransportSquare p ≃ (transportSquareSpace p) _⦋0⦌ where
  toFun := transportSquareVertex
  invFun := transportSquareOfVertex p
  left_inv S := transportSquareVertex_injective p
    (transportSquareVertex_ofVertex p (transportSquareVertex S))
  right_inv := transportSquareVertex_ofVertex p

end SerrePositivity.InfinityCategories
