module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionTriangle

/-!
概要：元の弱い retract の非分裂点を指定し、元の強い分裂と実際の三角形へ照合する。
方針：元の二単体の中央頂点を最初の辺の終点として取る。
規約：元の二点への写像の厳密な等式を保持する。
使われ方：右 fibration に持ち上げた元の retract の両対象を回収する。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の弱い retract の元の非分裂点。 -/
def weakSourcePoint : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape :=
  stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle

/-- 元の比較は元の非分裂点を同じ強い分裂添字の点へ送る。 -/
lemma weakComparison_sourcePoint : weakSourcePoint ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison.{u} =
    SSet.yonedaEquiv.symm (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource) := by
  simp only [weakSourcePoint, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_triangle,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle_section]
  exact (nerve.edgeMk _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection).δ_zero_yonedaEquiv_symm

/-- 元の分裂三角形から作った弱い全図式は、元の非分裂点を厳密に保持する。 -/
lemma RetractionTriangle.weakDiagram_sourcePoint {X : SSet.{u}} {x y : X _⦋0⦌}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionTriangle x y) :
    weakSourcePoint ≫ t.weakDiagram = SSet.yonedaEquiv.symm x := by
  simp only [weakSourcePoint, Category.assoc, t.weakDiagram_section]
  exact t.1.δ_zero_yonedaEquiv_symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
