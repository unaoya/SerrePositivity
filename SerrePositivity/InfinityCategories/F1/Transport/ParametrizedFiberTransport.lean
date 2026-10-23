module

public import SerrePositivity.InfinityCategories.F1.Transport.FiberTransportFamilyNaturality
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingVertices

/-!
概要：固定端点の写像空間全体から fiber 間の関手空間への実際の輸送射。
方針：区間模型の普遍的な辺の族を一括して持ち上げる。
規約：輸送の同値性はこの構成と区別して証明する。
使われ方：Kerodon Definition 5.2.8.1、Lemma 5.6.9.1 の比較射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定端点の全ての辺を被覆し、始点 fiber 全体を同時に持ち上げる輸送族。
方針：区間写像空間の普遍的な評価にパラメーター付き輸送を適用する。
規約：始点の係数射は恒等射。
使われ方：普遍的なパラメーター付き輸送の実際の証人。 -/
noncomputable def parametrizedFiberTransportFamily {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a b : B _⦋0⦌) :
    FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a))
      (intervalMappingUncurry (𝟙 (intervalMappingSpace a b))) :=
  fiberTransportFamily p (𝟙 _) _ (intervalMappingUncurry_zero _) (intervalMappingUncurry_one _)

/-- 概要：固定端点の写像空間全体に依存する fiber 間の輸送射。
方針：一括した持ち上げの終点を curry する。
規約：任意の底の left fibration に対して構成し、同値性は主張しない。
使われ方：Kerodon Definition 5.2.8.1、普遍 pointed-space fibration の局所的分類。 -/
noncomputable def parametrizedFiberTransport {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a b : B _⦋0⦌) :
    intervalMappingSpace a b ⟶ (ihom (vertexFiber p a)).obj (vertexFiber p b) :=
  (parametrizedFiberTransportFamily p a b).map

/-- 概要：普遍輸送を一本の辺に制限すると、その辺に沿う transport と関手同型。
方針：普遍的な持ち上げの parameter を辺の頂点に固定し、prism の比較を使う。
規約：任意の底の実際の辺に対して同型を構成する。
使われ方：パラメーター付き比較と既存の edgeTransport の接続。 -/
noncomputable def parametrizedFiberTransport_at_edgeIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    FunctorIso
      ((functorVertexEquiv _ _).symm
        ((parametrizedFiberTransport p a b).app _ (intervalMappingVertexOfEdge e)))
      (edgeTransport p e) := by
  let T := parametrizedFiberTransportFamily p a b
  let v := intervalMappingVertexOfEdge e
  let j : vertexFiber p a ⟶ vertexFiber p a ⊗ intervalMappingSpace a b :=
    lift (𝟙 _) (SSet.const v)
  let g := j ≫ T.endpoint
  let H := (Δ[1] ◁ j) ≫ T.prism
  have h₀ : prismEndpoint 0 (vertexFiber p a) ≫ H = vertexFiberι p a := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start,
      ← Category.assoc, ← Category.assoc]
    change (j ≫ fst _ _) ≫ (𝟙 _ ≫ vertexFiberι p a) = _
    rw [lift_fst, Category.id_comp, Category.id_comp]
  have h₁ : prismEndpoint 1 (vertexFiber p a) ≫ H = g ≫ vertexFiberι p b := by
    dsimp only [H, g]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.finish, Category.assoc]
  have hp : H ≫ p = fst (Δ[1] : SSet.{u}) (vertexFiber p a) ≫
      SSet.yonedaEquiv.symm e.edge := by
    dsimp only [H]
    rw [Category.assoc, T.over_base, ← Category.assoc]
    have hj : (Δ[1] ◁ j) ≫ (Δ[1] ◁ snd (vertexFiber p a) (intervalMappingSpace a b)) =
        fst (Δ[1] : SSet.{u}) (vertexFiber p a) ≫
          lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const v) := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro s
      rfl
    rw [hj, Category.assoc, intervalMappingUniversal_at_edge]
  have he : g = (functorVertexEquiv _ _).symm
      ((parametrizedFiberTransport p a b).app _ v) := by
    have h := uncurry_at_vertex T.map v
    rw [FiberTransportFamily.map, uncurry_curry] at h
    exact h
  have h := leftFibrationPrism_transportIso p e (𝟙 _) g H
    (by simpa only [Category.id_comp] using h₀) h₁ hp
  rw [he, Category.id_comp] at h
  exact h

end SerrePositivity.InfinityCategories
