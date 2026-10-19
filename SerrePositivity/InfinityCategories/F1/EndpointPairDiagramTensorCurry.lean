module

public import SerrePositivity.InfinityCategories.F1.EndpointPairTransformationVertices
public import SerrePositivity.InfinityCategories.F1.CoherentTransformationFamilyNaturality

/-!
概要：積の底上の境界固定図式を元の底上の変換のパラメーター族へ curry する。
方針：普遍図式の四変数を並べ替え固定端点の変換空間へ戻す。
規約：高次パラメーターを全て保持する実際の単体集合の射。
使われ方：境界固定で得た変換の同型を族全体の関手同型へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底とパラメーターの結合を変更しても prism の端点条件は保たれる。
方針：端点の自然性と積の第一成分の計算を使う。
規約：i は任意の端点。
使われ方：四変数の普遍図式の固定端点。 -/
lemma coherentPrismTensorExchange_endpoint {B K L X : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ ((B ⊗ K) ⊗ L) ⟶ X) (F : B ⟶ X) (i : Fin 2)
    (hi : prismEndpoint i ((B ⊗ K) ⊗ L) ≫ H = fst (B ⊗ K) L ≫ (fst B K ≫ F)) :
    prismEndpoint i (B ⊗ (K ⊗ L)) ≫ ((Δ[1] ◁ (α_ B K L).inv) ≫ H) =
      fst B (K ⊗ L) ≫ F := by
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hi]
  rfl

/-- 概要：積の底上の固定境界図式を元の底上の変換の族へ移す。
方針：普遍図式の結合を変更し変換空間へ curry して再びパラメーターを curry する。
規約：底とパラメーターの小ささや Kan 性は不要。
使われ方：普遍パラメーター上の比較から左逆の関手同型を作る。 -/
def endpointPairDiagramTensorCurry (B K : SSet.{u + 1}) (F G : B ⟶ SpaceInfinity.{u}) :
    endpointPairDiagramSpace (fst B K ≫ F) (fst B K ≫ G) ⟶
      (ihom K).obj (leftUnstraighteningTransformationSpace F G) :=
  let A := endpointPairDiagramSpace (fst B K ≫ F) (fst B K ≫ G)
  let q := vertexFiberι ((pre (prismEndpointPair (B ⊗ K))).app SpaceInfinity)
    (functorVertex (joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)))
  let H := (α_ Δ[1] (B ⊗ K) A).inv ≫ uncurry q
  let he := endpointPairDiagramFamily_endpoints (fst B K ≫ F) (fst B K ≫ G) q
    (vertexFiberι_comp _ _)
  curry (coherentTransformationFamilyCurry F G ((Δ[1] ◁ (α_ B K A).inv) ≫ H)
    (coherentPrismTensorExchange_endpoint H F 0 he.1)
    (coherentPrismTensorExchange_endpoint H G 1 he.2))

/-- 概要：積の底上の図式 H の頂点は H を curry した変換の族の関手頂点となる。
方針：curry の頂点評価と普遍図式の頂点評価を続ける。
規約：元の図式 H は厳密に回収する。
使われ方：境界固定の変換の同型を実際の二つの族の関手同型へ戻す。 -/
lemma endpointPairDiagramTensorCurry_vertex {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ F)
    (h₁ : prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ G)
    (hH : prismEndpointPair (B ⊗ K) ≫ H =
      joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)) :
    (endpointPairDiagramTensorCurry B K F G).app _
      (fixedDiagramVertex (prismEndpointPair (B ⊗ K))
        (joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)) H hH) =
      functorVertex (coherentTransformationFamilyCurry F G H h₀ h₁) := by
  let A := endpointPairDiagramSpace (fst B K ≫ F) (fst B K ≫ G)
  let q := vertexFiberι ((pre (prismEndpointPair (B ⊗ K))).app SpaceInfinity)
    (functorVertex (joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)))
  let x : A _⦋0⦌ := fixedDiagramVertex (prismEndpointPair (B ⊗ K))
    (joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)) H hH
  have hq : lift (𝟙 (Δ[1] ⊗ (B ⊗ K))) (SSet.const x) ≫ uncurry q = H :=
    (uncurry_at_vertex q x).trans ((functorVertexEquiv _ _).symm_apply_apply H)
  dsimp only [endpointPairDiagramTensorCurry]
  rw [simplicialCurry_vertex]
  apply congrArg functorVertex
  apply coherentTransformationFamilyCurry_comp
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, b⟩, k⟩
  exact congrArg (fun f : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u} ↦
    f.app n (t, (b, k))) hq

end SerrePositivity.InfinityCategories
