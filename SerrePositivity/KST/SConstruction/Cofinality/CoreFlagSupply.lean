module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeSEdgeDetection
public import SerrePositivity.KST.LocalizingInvariants.CoreFlag.All

/-!
概要：到着した Sp-8 (1)・(2) の実証明を元の相対障害の入力へ代入する。
方針：元の対角制限を公開 counit と照合し、群 nerve の消滅を公開型へ直接渡す。
規約：一般供給を公理として複製せず、明示入力を実証明で消去する。
使われ方：元の相対先頭実現の無条件な高次消滅と相対 fiber への接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：Sp-8 (1) の元の対角評価を既存の明示入力へ代入する。
方針：同じ wide 模型の quasicategory 性を使い、公開 counit の弱同値を渡す。
規約：対角制限との等号は元の全高次単体で確認する。
使われ方：元の相対旗の対角評価の供給仮定の消去。 -/
def completionCoreFlagEvaluationInput (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    CompletionCoreFlagEvaluationInput r ι f := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  let : Quasicategory (LocalizingInvariants.completionCofiberWide F.val : SSet.{u}) :=
    LocalizingInvariants.completionCofiberWide_quasicategory F.val
      (multiSEndofunctor_map_isIdempotentCompletion r ι f hf)
  exact {
    evaluation := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.counit _
    diagonal_eq := by intro n v; rfl
    isWeak := LocalizingInvariants.CoreFlag.counit_isWeakHomotopyEquivalence _ }

/-- 概要：Sp-8 (2) の群 nerve の高次消滅を既存の一般入力へ代入する。
方針：同じ連続 Kan 置換と実次数の公開定理を直接使う。
規約：一般入力は実証明であり公理ではない。
使われ方：元の bar 障害の供給仮定の消去。 -/
theorem groupNerveHigherVanishingInput : GroupNerveHigherVanishingInput.{u} := by
  intro G hG n hn x
  let : Group G := hG
  exact LocalizingInvariants.CoreFlag.groupNerve_continuousKanReplacement_kanHomotopy_subsingleton
    G n hn x

/-- 概要：元の相対旗の wide 対角評価は弱ホモトピー同値。
方針：Sp-8 (1) の実供給を元の条件付き比較へ代入する。
規約：元の対角評価の射を変更しない。
使われ方：相対旗と元の wide 亜群化の比較。 -/
theorem completionRelativeFlagWideEvaluation_isWeak (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (completionRelativeFlagWideEvaluation r ι f hf) :=
  completionRelativeFlagWideEvaluation_isWeak_of_input r ι f hf
    (completionCoreFlagEvaluationInput r ι f hf)

/-- 概要：元の S 余核図式の二次以上のホモトピーは一意。
方針：元の bar 同型へ Sp-8 (2) の実供給を代入する。
規約：元の指定射の余核図式を保持する。
使われ方：同じ障害群の無条件な高次消滅。 -/
theorem cutCokernel_higher_subsingleton {X Y : StableModel.{u}} (f : X ⟶ Y)
    (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (cutCokernelSimplicialSet f)) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (cutCokernelSimplicialSet f)) n x) :=
  cutCokernel_higher_of_input groupNerveHigherVanishingInput f n hn x

/-- 概要：元の相対先頭実現の二次以上のホモトピーは一意。
方針：元の自然な対角評価と bar 同定へ Sp-8 (1)・(2) の実証明を代入する。
規約：一般 core 旗比較や群 nerve 消滅を追加仮定に残さない。
使われ方：K-B2-S1 相対 fiber 比較へ渡す右項の高次消滅。 -/
theorem completionRelativeHead_higher_subsingleton (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (completionRelativeHeadRealization r ι f hf)) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (completionRelativeHeadRealization r ι f hf)) n x) :=
  completionRelativeHead_higher_of_input groupNerveHigherVanishingInput r ι f hf
    (fun m => completionCoreFlagEvaluationInput (r + 1)
      ((completionCokernelHeadIndex r ι).obj m) f hf) n hn x

end SerrePositivity.KST.SConstruction.Cofinality
