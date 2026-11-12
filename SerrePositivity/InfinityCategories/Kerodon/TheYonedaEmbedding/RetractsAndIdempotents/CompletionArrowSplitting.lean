module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionArrow
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionStrongSplitting

/-!
概要：元の完備化の任意の辺を、元の圏の辺の像上の全 coherent 冪等図式の分裂として表示。
方針：全辺の関手圏内の実際の retract を、元の両頂点を固定した強い全分裂へ戻す。
規約：Idem 全体・Split 全体の図式と、元の両辺を厳密に保持する。
使われ方：HA 1.1.3.7 の新しい辺の fiber/cofiber の構成の入力。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の任意の辺は、元の始域の辺の像を非分裂点とする全 coherent 分裂の分裂点。 -/
lemma IsIdempotentCompletion.arrow_strongSplitting {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    (a : (Δ[1] : SSet.{u}) ⟶ D) :
    ∃ (b : (Δ[1] : SSet.{u}) ⟶ C)
      (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent ((ihom (Δ[1] : SSet.{u})).obj D)) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d),
      s.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a ∧ d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (b ≫ f) := by
  obtain ⟨b, ⟨r⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.arrow_retract f hf a
  obtain ⟨d, s, hx, hy⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction.strongSplitting_exists r
  exact ⟨b, d, s, hx, hy⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
