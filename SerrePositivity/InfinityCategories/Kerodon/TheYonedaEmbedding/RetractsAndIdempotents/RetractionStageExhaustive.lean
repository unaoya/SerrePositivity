module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AbsorbingChainFace
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdentityCollapseChain

/-!
概要：元の交互セルの像の増大列は、元の強い分裂添字全体を覆う。
方針：恒等値の隣接射は退化を与え、非退化単体は元の交互セルの面となる。
規約：退化単体も元の単体作用によって同じ像の増大列へ戻す。
使われ方：Ret(1) の包含の inner anodyne 性を無限合成へ接続する。

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

/-- 元の恒等値の隣接射があれば、元の全単体は元の nerve の退化単体。 -/
lemma walkingChain_degenerate_of_one {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} (n + 1))
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar (F.map (homOfLE i.castSucc_le_succ)).f = 1) :
    F ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.degenerate (n + 1) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.σ i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.δ i.succ F) = F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.identityCollapse_chain_eq i F h
  rw [← he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.σ_mem_degenerate i _

/-- 元の非退化単体の隣接射は、全て元の吸収射。 -/
lemma walkingChain_nondegenerate_absorbing {n : ℕ}
    (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n) (hF : F ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.nonDegenerate n)
    (i : ℕ) (hi : i < n) : F.map' i (i + 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _ := by
  cases n with
  | zero => omega
  | succ n =>
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingHom_cases (F.map' i (i + 1)) with h | ⟨_, _, h⟩
    · exact h
    · exact False.elim (hF (walkingChain_degenerate_of_one ⟨i, hi⟩ F h))

/-- 元の全単体は、退化も含めて元の第 n+1 段階に属する。 -/
lemma retractionStage_contains_simplex {n : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.{u} _⦋n⦌) :
    F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage (n + 1)).obj (Opposite.op ⦋n⦌) := by
  obtain ⟨m, f, hf, y, hy⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.exists_nonDegenerate F
  have hm : m ≤ n := SimplexCategory.le_of_epi f
  have hmem := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.absorbingChain_mem_stage y.val (walkingChain_nondegenerate_absorbing y.val y.prop)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage_mono (Nat.succ_le_succ hm)
  rw [hy]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage (m + 1)).map f.op hmem

/-- 元の第一段階以後の像の増大列は、元の分裂添字全体を覆う。 -/
lemma retractionStage_iSup_succ : (⨆ m : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage.{u} (m + 1)) = ⊤ := by
  apply top_unique
  intro n F _hF
  rcases n with ⟨⟨n⟩⟩
  rw [Subfunctor.iSup_obj]
  exact Set.mem_iUnion.mpr ⟨n, retractionStage_contains_simplex F⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
