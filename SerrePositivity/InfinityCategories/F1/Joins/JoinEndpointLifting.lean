module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinEndpointComparison
public import SerrePositivity.InfinityCategories.Core.FixedDiagramVertexEquiv
public import SerrePositivity.InfinityCategories.Core.FixedDiagramHomotopy

/-!
概要：両端を固定した fat join 図式を通常の join 図式でホモトピーまで回収する。
方針：固定図式上の比較の本質的全射性を使い、その頂点の同型を相対ホモトピーで表す。
規約：両端はホモトピーの全時刻で厳密に固定する。
使われ方：Kerodon §4.6.5–4.6.6、区間模型の族から pinched 模型への逆の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：両端を固定した fat join 図式は通常の join 図式の像と相対的にホモトピック。
方針：固定 fiber の同値から図式を選び、同型を両端固定の可逆ホモトピーに移す。
規約：A,B は任意、X にだけ quasicategory 性を要求する。
使われ方：Kerodon §4.6.5–4.6.6、写像空間の比較射のホモトピー逆の回収。 -/
lemma exists_joinDiagram_of_fatJoinDiagram {A B X : SSet.{u}} [Quasicategory X]
    (p : joinEndpointDiagram A B ⟶ X) (F : fatJoin A B ⟶ X)
    (hF : fatJoinEndpointInclusion A B ≫ F = p) :
    ∃ G : join A B ⟶ X, ∃ _hG : joinEndpointInclusion A B ≫ G = p,
      ∃ H : SSet.Homotopy (fatJoinComparison A B ≫ G) F,
        (fatJoinEndpointInclusion A B ▷ (Δ[1] : SSet.{u})) ≫ H.h =
          fst (joinEndpointDiagram A B) Δ[1] ≫ p ∧
        ∀ v, IsInvertibleEdge (simplicialHomotopyVertexEdge H v).toTruncated := by
  let v := fixedDiagramVertex (fatJoinEndpointInclusion A B) p F hF
  obtain ⟨w, ⟨e⟩⟩ :=
    (isQCatEquivalence_fatJoinComparison_fixedEndpoints A B X p).choose.isEssentiallySurjective v
  obtain ⟨⟨G, hG⟩, rfl⟩ := (fixedDiagramVertexEquiv (joinEndpointInclusion A B) p).surjective w
  have hGC : fatJoinEndpointInclusion A B ≫ (fatJoinComparison A B ≫ G) = p := by
    rw [← Category.assoc, fatJoinEndpointInclusion_comparison, hG]
  have he : VertexIso (X := vertexFiber ((pre (fatJoinEndpointInclusion A B)).app X)
      (functorVertex p))
      (fixedDiagramVertex (fatJoinEndpointInclusion A B) p (fatJoinComparison A B ≫ G) hGC)
      (fixedDiagramVertex (fatJoinEndpointInclusion A B) p F hF) := e
  obtain ⟨H, hH, hI⟩ := exists_relative_homotopy_of_fixedDiagram_vertexIso
    (fatJoinEndpointInclusion A B) p (fatJoinComparison A B ≫ G) F hGC hF he
  exact ⟨G, hG, H, hH, hI⟩

end SerrePositivity.InfinityCategories
