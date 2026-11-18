module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeEvaluationNaturality

/-!
概要：元の相対 core 旗の先頭実現を元の wide 先頭実現へ比較する。
方針：全多次数で自然な元の対角評価を、Sp-8 (1) 入力下で対角の弱同値に移す。
規約：一般 core 旗比較は明示入力として保持する。
使われ方：相対 fiber 供給の右項と元の障害群の接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial

/-- 概要：元の相対旗の対角実現を先頭 S 方向でも実現する。
方針：残りの全多次数を固定した元の図式へ対角関手を適用する。
規約：旗方向・core 方向・先頭 S 方向の元の全対角を保持する。
使われ方：相対 fiber 供給の右項と照合する未置換実現。 -/
def completionRelativeHeadRealization (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (completionCokernelHeadIndex r ι ⋙
    completionRelativeFlagRealizationDiagram (r + 1) f hf)

/-- 概要：元の相対旗の先頭実現から元の wide 先頭実現への評価。
方針：同じ元の対角評価の自然変換を先頭方向で対角化する。
規約：零段と元の標的への対角評価を取り替えない。
使われ方：元の相対障害の消滅への比較射。 -/
def completionRelativeHeadWideEvaluation (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionRelativeHeadRealization r ι f hf ⟶ completionWideHeadRealization r ι f hf :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (Functor.whiskerLeft (completionCokernelHeadIndex r ι)
    (completionRelativeWideEvaluationNat (r + 1) f hf))

/-- 概要：Sp-8 (1) 入力下で元の相対先頭評価は弱ホモトピー同値。
方針：各先頭次数で元の評価の弱同値を対角定理へ渡す。
規約：入力の各評価は同じ元の対角制限と一致しなければならない。
使われ方：元の相対障害への bar の高次消滅の移送。 -/
lemma completionRelativeHeadWideEvaluation_isWeak_of_input (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (input : ∀ n : SimplexCategoryᵒᵖ,
      CompletionCoreFlagEvaluationInput (r + 1) ((completionCokernelHeadIndex r ι).obj n) f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (completionRelativeHeadWideEvaluation r ι f hf) := by
  let τ := Functor.whiskerLeft (completionCokernelHeadIndex r ι)
    (completionRelativeWideEvaluationNat (r + 1) f hf)
  have hτ (n : SimplexCategoryᵒᵖ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (τ.app n) :=
    completionRelativeFlagWideEvaluation_isWeak_of_input (r + 1)
      ((completionCokernelHeadIndex r ι).obj n) f hf (input n)
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial.diagonalFunctor_map_weak τ hτ

/-- 概要：Sp-8 (1)・(2) 入力下で元の相対先頭実現の二次以上は一意。
方針：元の評価の Kan 置換の π 単射性で同じ wide 実現の消滅を引き戻す。
規約：相対 fiber 本体や主共終性の結論は仮定しない。
使われ方：元の相対 fiber 比較へ渡す右項の高次消滅。 -/
lemma completionRelativeHead_higher_of_input (h : GroupNerveHigherVanishingInput.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (input : ∀ m : SimplexCategoryᵒᵖ,
      CompletionCoreFlagEvaluationInput (r + 1) ((completionCokernelHeadIndex r ι).obj m) f)
    (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (completionRelativeHeadRealization r ι f hf)) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (completionRelativeHeadRealization r ι f hf)) n x) := by
  let p := completionRelativeHeadWideEvaluation r ι f hf
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence p
    (completionRelativeHeadWideEvaluation_isWeak_of_input r ι f hf input)
  have hπ := Spectra.kanPiIsomorphism_of_qCatEquivalence _
    hw.isSimplicialHomotopyEquivalence.isQCatEquivalence
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (completionWideHeadRealization r ι f hf)) n
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map p).app (Opposite.op ⦋0⦌) x)) :=
    completionWideHead_higher_of_input h r ι f hf n hn _
  exact Function.Injective.subsingleton ((hπ x n).1)

end SerrePositivity.KST.SConstruction.Cofinality
