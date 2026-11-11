module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeCoreFlagIso
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality

/-!
概要：一般評価の供給から同じ全多次数の相対旗の亜群化の離散性を得る。
方針：元の対角評価の Kan 置換を全基点 π 同型に移し、Sp-7 の正次数の一意性を引く。
規約：相対 S• の加法的 fiber 比較や主共終性をこの結論だけから推論しない。
使われ方：相対実現比較の離散的障害側。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：具体的な全辺 wide 模型の Kan 置換の正次数は一意。
方針：選択された供給値と全辺模型の等号で既存の離散性を輸送する。
規約：指定完備化射の同じ全多次数に特殊化する。
使われ方：対角評価で相対旗の正次数を検査する標的。 -/
lemma completionCanonicalWide_positive_subsingleton (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) _⦋0⦌)
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) n x) := by
  have he := completionMultiWide_eq r ι f hf
  have h : ∀ (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      ((multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex : SSet.{u})) _⦋0⦌),
      Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
        ((multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex : SSet.{u})) n z) :=
    fun z => completionMultiWide_positive_subsingleton r ι f hf z n hn
  rw [he] at h
  exact h x

/-- 概要：一般評価の供給を仮定すると、相対旗の対角の亜群化の全正次数は一意。
方針：元の相対評価の Kan 置換が誘導する全基点 π 同型の単射性を使う。
規約：一般供給だけを明示入力に残し、モデル構造の instance を要求しない。
使われ方：相対 fiber 比較の離散的障害の高次消滅。 -/
theorem completionRelativeFlag_positive_subsingleton_of_input (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (input : CompletionCoreFlagEvaluationInput r ι f)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      (completionRelativeFlagRealization r ι f hf)) _⦋0⦌) (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      (completionRelativeFlagRealization r ι f hf)) n x) := by
  let e := completionRelativeFlagWideEvaluation r ι f hf
  have hw := completionRelativeFlagWideEvaluation_isWeak_of_input r ι f hf input
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence e hw
  have hπ := kanPiIsomorphism_of_qCatEquivalence _
    hR.isSimplicialHomotopyEquivalence.isQCatEquivalence
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) n
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map e).app (Opposite.op ⦋0⦌) x)) :=
    completionCanonicalWide_positive_subsingleton r ι f hf _ n hn
  exact Function.Injective.subsingleton ((hπ x n).1)

end SerrePositivity.KST.SConstruction.Cofinality
