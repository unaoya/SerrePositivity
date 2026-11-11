module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HornCellExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
概要：具体的な可算セル付加の余極限は実際に Kan 複体である。
方針：有限ホーンを反復の一段へ下ろし、次の段に付加したセルで充填する。
規約：元の対象の Kan 性やモデル圏の追加仮定を置かない。
使われ方：filtered 余極限を保つ Kan 置換の値の充填性。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：余極限の後続段の脚とセル付加の単位の合成は元の段の脚。
方針：反復図式の後続射を余極限余錐の自然性へ代入する。
規約：指定した対象 X での射の等式。使われ方：一段先のホーン充填を余極限へ送る。 -/
lemma hornCellSequence_step_ι (X : SSet.{u}) (j : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCellStepUnit.app ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellStage.{u} j).obj X) ≫
      (colimit.ι _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u} (AsSmall.up.obj (j + 1))).app X =
        (colimit.ι _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u} (AsSmall.up.obj j)).app X := by
  have h := colimit.w _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u} (AsSmall.up.map (homOfLE (Nat.le_succ j)))
  change (Functor.ofSequence _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellStageMap).map (homOfLE (Nat.le_succ j)) ≫ _ = _ at h
  rw [Functor.ofSequence_map_homOfLE_succ] at h
  exact NatTrans.congr_app h X

/-- 概要：セル付加の可算反復の余極限の値は Kan 複体。
方針：有限表示性でホーンを一段へ下ろし、次段の実際のセルを余極限へ送る。
規約：既存の任意の Kan 置換の連続性には依存しない。
使われ方：一般の filtered ∞ 圏の弱可縮性で用いる連続な置換。 -/
instance continuousKanReplacement_kanComplex (X : SSet.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X) := by
  rw [KanComplex.iff]
  intro n i fs hf
  have hc := isColimitOfPreserves ((evaluation SSet.{u} SSet.{u}).obj X)
    (colimit.isColimit _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u})
  obtain ⟨j, t, ht⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc hf.desc
  obtain ⟨j⟩ := j
  change t ≫ (colimit.ι _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u} (AsSmall.up.obj j)).app X = hf.desc at ht
  let tj : (horn (n + 1) i : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellStage.{u} j).obj X := t
  have htj : tj ≫ (colimit.ι _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u} (AsSmall.up.obj j)).app X = hf.desc := ht
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.exists_hornCellStep_extension tj
  have h : (horn (n + 1) i).ι ≫
      (F ≫ (colimit.ι _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u} (AsSmall.up.obj (j + 1))).app X) = hf.desc := by
    rw [← Category.assoc, hF, Category.assoc, hornCellSequence_step_ι, htj]
  refine ⟨F ≫ (colimit.ι _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u} (AsSmall.up.obj (j + 1))).app X, fun k hk ↦ ?_⟩
  rw [← horn.ι_ι_assoc i k hk, h]
  exact hf.ι_desc k hk

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
