module

public import SerrePositivity.KST.Comparison.SimplicialSumFibrations
public import SerrePositivity.KST.Comparison.SimplicialSumEquivalences
public import SerrePositivity.KST.Comparison.FibrantSquareCriterion

/-!
# 添字付き余積のホモトピー引き戻し

概要：縦射が Kan fibration である成分ごとのホモトピー引き戻しを余積にまとめる。
方針：厳密ファイバーへの比較の可逆性を余積へ移し、余積の厳密な引き戻しを使う。
規約：Segal 1974 Lemma 1.8 の telescope の二面。添字の写像は任意。
使われ方：成分ごとの Kan 置換後に二重写像円筒の貼り合わせを適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel
variable {ι κ : Type v}

/--
概要：Kan な右縦射を持つ成分のホモトピー引き戻しは、添字を写す余積でもホモトピー引き戻しである。
方針：各厳密ファイバーへの比較を余積にまとめ、四頂点の局所化同型による不変性を使う。
規約：余積の基底や全空間の Kan 性は不要。
使われ方：telescope の偶数・奇数の二面への Lemma 1.7 の適用。
-/
theorem simplicialSumReindex_homotopyPullback_of_fibrations
    {A C : ι → SSet.{max u v}} {B D : κ → SSet.{max u v}} (σ : ι → κ)
    (a : ∀ i, A i ⟶ B (σ i)) (w : ∀ i, A i ⟶ C i)
    (v : ∀ j, B j ⟶ D j) (c : ∀ i, C i ⟶ D (σ i))
    (sq : ∀ i, CommSq (a i) (w i) (v (σ i)) (c i))
    (h : ∀ i, IsHomotopyPullback (sq i))
    (hv : ∀ j, SSet.modelCategoryQuillen.J.rlp (v j)) :
    IsHomotopyPullback (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_commSq σ a w v c sq) := by
  let E i := pullback (c i) (v (σ i))
  let k i : A i ⟶ E i := pullback.lift (w i) (a i) (sq i).w.symm
  have hk i : IsIso (AnodyneHomotopy.anodyneQ.map (k i)) :=
    (isHomotopyPullback_iff_strict_of_left_fibration (sq i) (hv (σ i))).mp (h i)
  let a' i : E i ⟶ B (σ i) := pullback.snd (c i) (v (σ i))
  let w' i : E i ⟶ C i := pullback.fst (c i) (v (σ i))
  have h' i : IsPullback (a' i) (w' i) (v (σ i)) (c i) :=
    (IsPullback.of_hasPullback (c i) (v (σ i))).flip
  have hs := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_isPullback σ a' w' v c h'
  have hp := isHomotopyPullback_of_left_fibration hs (simplicialSumMap_rlp v hv)
  apply (isHomotopyPullback_iff_of_localized_isIso
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_commSq σ a w v c sq) hs.toCommSq
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap k) (𝟙 _) (𝟙 _) (𝟙 _) ?_ ?_ (by simp) (by simp)
    (simplicialSumMap_localized_isIso k hk) (by infer_instance)
    (by infer_instance) (by infer_instance)).mpr hp
  · apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext
    intro i
    change a i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion B (σ i) =
      (k i ≫ a' i) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion B (σ i)
    simp [k, a']
  · apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext
    intro i
    change w i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion C i =
      (k i ≫ w' i) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion C i
    simp [k, w']

end SerrePositivity.KST.Comparison
