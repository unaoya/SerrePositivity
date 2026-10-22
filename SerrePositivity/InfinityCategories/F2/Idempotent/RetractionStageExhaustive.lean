module

public import SerrePositivity.InfinityCategories.F2.Idempotent.AbsorbingChainFace
public import SerrePositivity.InfinityCategories.F2.Idempotent.IdentityCollapseChain

/-!
概要：元の交互セルの像の増大列は、元の強い分裂添字全体を覆う。
方針：恒等値の隣接射は退化を与え、非退化単体は元の交互セルの面となる。
規約：退化単体も元の単体作用によって同じ像の増大列へ戻す。
使われ方：Ret(1) の包含の inner anodyne 性を無限合成へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の恒等値の隣接射があれば、元の全単体は元の nerve の退化単体。 -/
lemma walkingChain_degenerate_of_one {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows WalkingSplit.{u} (n + 1))
    (h : walkingScalar (F.map (homOfLE i.castSucc_le_succ)).f = 1) :
    F ∈ SplitShape.degenerate (n + 1) := by
  have he : SplitShape.σ i (SplitShape.δ i.succ F) = F := identityCollapse_chain_eq i F h
  rw [← he]
  exact SplitShape.σ_mem_degenerate i _

/-- 元の非退化単体の隣接射は、全て元の吸収射。 -/
lemma walkingChain_nondegenerate_absorbing {n : ℕ}
    (F : ComposableArrows WalkingSplit.{u} n) (hF : F ∈ SplitShape.nonDegenerate n)
    (i : ℕ) (hi : i < n) : F.map' i (i + 1) = walkingAbsorbingHom _ _ := by
  cases n with
  | zero => omega
  | succ n =>
    rcases walkingHom_cases (F.map' i (i + 1)) with h | ⟨_, _, h⟩
    · exact h
    · exact False.elim (hF (walkingChain_degenerate_of_one ⟨i, hi⟩ F h))

/-- 元の全単体は、退化も含めて元の第 n+1 段階に属する。 -/
lemma retractionStage_contains_simplex {n : ℕ} (F : SplitShape.{u} _⦋n⦌) :
    F ∈ (retractionStage (n + 1)).obj (Opposite.op ⦋n⦌) := by
  obtain ⟨m, f, hf, y, hy⟩ := SplitShape.exists_nonDegenerate F
  have hm : m ≤ n := SimplexCategory.le_of_epi f
  have hmem := absorbingChain_mem_stage y.val (walkingChain_nondegenerate_absorbing y.val y.prop)
  apply retractionStage_mono (Nat.succ_le_succ hm)
  rw [hy]
  exact (retractionStage (m + 1)).map f.op hmem

/-- 元の第一段階以後の像の増大列は、元の分裂添字全体を覆う。 -/
lemma retractionStage_iSup_succ : (⨆ m : ℕ, retractionStage.{u} (m + 1)) = ⊤ := by
  apply top_unique
  intro n F _hF
  rcases n with ⟨⟨n⟩⟩
  rw [Subfunctor.iSup_obj]
  exact Set.mem_iUnion.mpr ⟨n, retractionStage_contains_simplex F⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
