module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalNativeComparison

/-!
概要：元の余極限指定辺と a6 の native 辺の比較を、両端固定の全円柱に戻す。
方針：区間写像空間の指定同型を表す辺を取り、同じ fiber 包含で展開する。
規約：同型の類・元の辺・両端の全時間の固定を保持。使われ方：全錐の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- a6 の選択済み native 辺を元の両端の区間模型で表示した頂点。 -/
def coherentColimitNativeIntervalVertex :=
  (pinchedHomLeftToIntervalMappingSpace (coherentDiagramTotalCocone F).vertex
    (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
      (coherentTotalMapNativeRepresentation F G
        (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))).1

/-- 指定比較同型を表す、同じ端点固定写像空間の実際の辺。 -/
def coherentColimitIntervalNativeEdge : SSet.Truncated.Edge
    (X := (truncation 2).obj (intervalMappingSpace (coherentDiagramTotalCocone F).vertex
      (coherentDiagramTotalVertex G)))
    (coherentColimitIntervalVertex B H) (coherentColimitNativeIntervalVertex B H) :=
  Classical.choose (homotopyCategory_homMk_surjective _ _
    (coherentColimitIntervalNativeIso B H).hom)

/-- 選んだ比較辺の類は元の指定比較同型の順方向そのもの。 -/
lemma coherentColimitIntervalNativeEdge_hom :
    SSet.Truncated.HomotopyCategory.homMk (coherentColimitIntervalNativeEdge B H) =
      (coherentColimitIntervalNativeIso B H).hom :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _
    (coherentColimitIntervalNativeIso B H).hom)

/-- 元の余極限指定辺から native 辺の同じ区間表示へ向かう実円柱。 -/
def coherentColimitIntervalNativeHomotopy :
    SSet.Homotopy (SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B H).edge)
      ((functorVertexEquiv (Δ[1] : SSet.{u + 1}) SpaceInfinity.{u}).symm
        (coherentColimitNativeIntervalVertex B H).val) := by
  let e := (coherentColimitIntervalNativeEdge B H).map ((truncation 2).map
    (vertexFiberι ((pre (boundary 1).ι).app SpaceInfinity.{u})
      (functorVertex (intervalMappingBoundary (coherentDiagramTotalCocone F).vertex
        (coherentDiagramTotalVertex G)))))
  refine simplicialHomotopyOfFunctorEdge ⟨e.edge, e.src_eq, e.tgt_eq.trans ?_⟩
  exact ((functorVertexEquiv (Δ[1] : SSet.{u + 1}) SpaceInfinity.{u}).apply_symm_apply _).symm

/-- 同じ比較円柱は、元の端点固定写像空間の比較辺の全区間展開そのもの。 -/
lemma coherentColimitIntervalNativeHomotopy_h :
    (coherentColimitIntervalNativeHomotopy B H).h = intervalMappingUncurry
      (SSet.yonedaEquiv.symm (coherentColimitIntervalNativeEdge B H).edge) := by
  change uncurry (SSet.yonedaEquiv.symm ((vertexFiberι
    ((pre (boundary 1).ι).app SpaceInfinity.{u})
      (functorVertex (intervalMappingBoundary (coherentDiagramTotalCocone F).vertex
        (coherentDiagramTotalVertex G)))).app (Opposite.op ⦋1⦌)
          (coherentColimitIntervalNativeEdge B H).edge)) = _
  rw [← SSet.yonedaEquiv_symm_comp]
  rfl

/-- 始点は比較円柱の全時刻で元の余極限始域頂点に固定。 -/
lemma coherentColimitIntervalNativeHomotopy_source :
    prismEndpoint 0 Δ[1] ≫ (coherentColimitIntervalNativeHomotopy B H).h =
      SSet.const (coherentDiagramTotalCocone F).vertex := by
  rw [coherentColimitIntervalNativeHomotopy_h, intervalMappingUncurry_zero]

/-- 終点も比較円柱の全時刻で元の余極限標的頂点に固定。 -/
lemma coherentColimitIntervalNativeHomotopy_target :
    prismEndpoint 1 Δ[1] ≫ (coherentColimitIntervalNativeHomotopy B H).h =
      SSet.const (coherentDiagramTotalVertex G) := by
  rw [coherentColimitIntervalNativeHomotopy_h, intervalMappingUncurry_one]

end SerrePositivity.InfinityCategories.F2
