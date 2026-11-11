module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.EndpointPairTransformationVertices
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyNaturality

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
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：底とパラメーターの結合を変更しても prism の端点条件は保たれる。
方針：端点の自然性と積の第一成分の計算を使う。
規約：i は任意の端点。
使われ方：四変数の普遍図式の固定端点。 -/
lemma coherentPrismTensorExchange_endpoint {B K L X : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ ((B ⊗ K) ⊗ L) ⟶ X) (F : B ⟶ X) (i : Fin 2)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i ((B ⊗ K) ⊗ L) ≫ H = fst (B ⊗ K) L ≫ (fst B K ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (B ⊗ (K ⊗ L)) ≫ ((Δ[1] ◁ (α_ B K L).inv) ≫ H) =
      fst B (K ⊗ L) ≫ F := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hi]
  rfl

/-- 概要：積の底上の固定境界図式を元の底上の変換の族へ移す。
方針：普遍図式の結合を変更し変換空間へ curry して再びパラメーターを curry する。
規約：底とパラメーターの小ささや Kan 性は不要。
使われ方：普遍パラメーター上の比較から左逆の関手同型を作る。 -/
def endpointPairDiagramTensorCurry (B K : SSet.{u + 1}) (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.endpointPairDiagramSpace (fst B K ≫ F) (fst B K ≫ G) ⟶
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) :=
  let A := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.endpointPairDiagramSpace (fst B K ≫ F) (fst B K ≫ G)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair (B ⊗ K))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)))
  let H := (α_ Δ[1] (B ⊗ K) A).inv ≫ uncurry q
  let he := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.endpointPairDiagramFamily_endpoints (fst B K ≫ F) (fst B K ≫ G) q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _)
  curry (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry F G ((Δ[1] ◁ (α_ B K A).inv) ≫ H)
    (coherentPrismTensorExchange_endpoint H F 0 he.1)
    (coherentPrismTensorExchange_endpoint H G 1 he.2))

/-- 概要：積の底上の図式 H の頂点は H を curry した変換の族の関手頂点となる。
方針：curry の頂点評価と普遍図式の頂点評価を続ける。
規約：元の図式 H は厳密に回収する。
使われ方：境界固定の変換の同型を実際の二つの族の関手同型へ戻す。 -/
lemma endpointPairDiagramTensorCurry_vertex {B K : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ F)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ G)
    (hH : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair (B ⊗ K) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)) :
    (endpointPairDiagramTensorCurry B K F G).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramVertex (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair (B ⊗ K))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)) H hH) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry F G H h₀ h₁) := by
  let A := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.endpointPairDiagramSpace (fst B K ≫ F) (fst B K ≫ G)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair (B ⊗ K))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)))
  let x : A _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramVertex (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair (B ⊗ K))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (fst B K ≫ F) (fst B K ≫ G)) H hH
  have hq : lift (𝟙 (Δ[1] ⊗ (B ⊗ K))) (SSet.const x) ≫ uncurry q = H :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uncurry_at_vertex q x).trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply H)
  dsimp only [endpointPairDiagramTensorCurry]
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.simplicialCurry_vertex]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyCurry_comp
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, b⟩, k⟩
  exact congrArg (fun f : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} ↦
    f.app n (t, (b, k))) hq

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
