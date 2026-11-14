module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.SimplicialSumPullbacks
public import SerrePositivity.KST.Comparison.FibrationLocality

/-!
# 添字付き余積の Kan fibration

概要：成分ごとの Kan fibration の余積は Kan fibration である。
方針：標準単体からの射を Yoneda で一つの成分へ移し、包含の引き戻しを使う。
規約：Segal 1974 Lemma 1.8 の telescope の二面の比較。
使われ方：縦射を Kan fibration とした余積のホモトピー引き戻しの判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open scoped Simplicial
variable {ι : Type v}

/--
概要：添字を保つ Kan fibration の余積は Kan fibration である。
方針：標準単体の像の添字を固定し、その成分への引き戻しで horn を充填する。
規約：成分の対象の Kan 性は不要。
使われ方：余積の四角形のホモトピー引き戻し性。
-/
theorem simplicialSumMap_rlp {A B : ι → SSet.{max u v}} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, SSet.modelCategoryQuillen.J.rlp (f i)) :
    SSet.modelCategoryQuillen.J.rlp (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap f) := by
  intro P D j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  apply lifting_of_pullbackFactorizations (SSet.horn (n + 1) k).ι (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap f)
  intro b
  let x := SSet.yonedaEquiv b
  refine ⟨B x.1, A x.1, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion B x.1, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion A x.1,
    f x.1, SSet.yonedaEquiv.symm x.2, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_isPullback f x.1,
    hf x.1 _ (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) k), ?_⟩
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.KST.Comparison
