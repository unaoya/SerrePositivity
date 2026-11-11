module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingClassification
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionStages
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.OddDeletion

/-!
概要：隣接射が元の吸収射である全 nerve 単体を、元の交互セルの面へ入れる。
方針：第 i 頂点を 2i または 2i+1 に置き、元の二対象と全隣接射を照合する。
規約：頂点だけでなく、元の nerve 単体全体の等式を証明する。
使われ方：Ret の像の増大列の全被覆性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の第 i 頂点を、同じ対象を持つ交互列の第 2i または 2i+1 位置へ置く。 -/
def absorbingChainPosition {n : ℕ} (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n)
    (i : Fin (n + 1)) : Fin (2 * (n + 1) + 1) :=
  ⟨2 * i.val + if F.obj i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource then 1 else 0, by
    split_ifs <;> have := i.isLt <;> omega⟩

/-- 元の位置の選択は、元の頂点順序を厳密に保つ。 -/
lemma absorbingChainPosition_strictMono {n : ℕ} (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n) :
    StrictMono (absorbingChainPosition F) := by
  intro i j h
  change (absorbingChainPosition F i).val < (absorbingChainPosition F j).val
  dsimp only [absorbingChainPosition]
  split_ifs <;> change i.val < j.val at h <;> omega

/-- 元の位置の選択は、元の有限順序の射。 -/
def absorbingChainFaceMap {n : ℕ} (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n) :
    ⦋n⦌ ⟶ ⦋2 * (n + 1)⦌ :=
  SimplexCategory.Hom.mk ⟨absorbingChainPosition F, (absorbingChainPosition_strictMono F).monotone⟩

/-- 元の選択位置にある交互列の対象は、元の単体の同じ対象そのもの。 -/
lemma absorbingChainPosition_obj {n : ℕ} (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n)
    (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject (absorbingChainPosition F i).val = F.obj i := by
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSplit_object_cases (F.obj i) with h | h
  · simp [absorbingChainPosition, h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject]
  · simp [absorbingChainPosition, h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject, Ne.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource_ne_image]

/-- 元の隣接射が吸収射なら、元の全単体は元の交互セルの同じ面への制限。 -/
lemma absorbingChainFace_eq {n : ℕ} (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n)
    (hF : ∀ (i : ℕ) (hi : i < n), F.map' i (i + 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _) :
    (SimplexCategory.toCat.map (absorbingChainFaceMap F)).toFunctor ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain (2 * (n + 1)) = F := by
  change (absorbingChainPosition_strictMono F).monotone.functor ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain (2 * (n + 1)) = F
  refine ComposableArrows.ext (absorbingChainPosition_obj F) ?_
  intro i hi
  have hne : absorbingChainPosition F ⟨i, by omega⟩ ≠
      absorbingChainPosition F ⟨i + 1, by omega⟩ :=
    (absorbingChainPosition_strictMono F).injective.ne (by
      intro h
      have hv := congrArg Fin.val h
      change i = i + 1 at hv
      omega)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap (absorbingChainPosition F ⟨i, by omega⟩)
    (absorbingChainPosition F ⟨i + 1, by omega⟩) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap, dite_eq_right hne, hF i hi]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom_transport (absorbingChainPosition_obj F ⟨i, by omega⟩)
    (absorbingChainPosition_obj F ⟨i + 1, by omega⟩)).symm

/-- 元の全隣接射が吸収射である単体は、元の第 n+1 段階に属する。 -/
lemma absorbingChain_mem_stage {n : ℕ} (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n)
    (hF : ∀ (i : ℕ) (hi : i < n), F.map' i (i + 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _) :
    F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage (n + 1)).obj (Opposite.op ⦋n⦌) := by
  refine ⟨SSet.stdSimplex.objEquiv.symm (absorbingChainFaceMap F), ?_⟩
  exact absorbingChainFace_eq F hF

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
