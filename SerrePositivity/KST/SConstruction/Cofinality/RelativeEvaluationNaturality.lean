module
public import SerrePositivity.KST.SConstruction.Cofinality.WideHeadVanishing

/-!
概要：元の相対 core 旗の対角評価を全 S 多次数の自然変換に束ねる。
方針：相対旗の構造射を core と対角へ写し、元の対角評価との可換性を計算する。
規約：評価射は元の対角制限のまま保持する。
使われ方：元の相対旗の先頭実現から wide 実現への比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の相対 core 旗の対角実現を全 S 多次数で束ねる。
方針：元の全旗図式に core と対角関手を適用する。
規約：各多次数の対象は元の completionRelativeFlagRealization。
使われ方：評価の全多次数自然性の始域。 -/
def completionRelativeFlagRealizationDiagram (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u} :=
  completionRelativeFlagDiagram r f hf ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor ⋙
      simplicialDiagonalFunctor

/-- 概要：元の相対 core 旗の対角評価は全 S 多次数で自然。
方針：各単体の元の対角制限と後合成が厳密に可換であることを計算する。
規約：元の評価射も元の wide 構造射も変更しない。
使われ方：相対旗と wide の元の先頭実現の比較。 -/
def completionRelativeWideEvaluationNat (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionRelativeFlagRealizationDiagram r f hf ⟶ completionCanonicalWideDiagram r f hf where
  app ι := completionRelativeFlagWideEvaluation r ι f hf
  naturality {_ _} α := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    rfl

end SerrePositivity.KST.SConstruction.Cofinality
