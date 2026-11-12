module
public import SerrePositivity.KST.SConstruction.Cofinality.SourceRelativeFlags
public import SerrePositivity.KST.LocalizingInvariants.IdempotentCompletionCofiberGroupoid

/-!
概要：Sp-7 の証明済みの一般供給を元の完備化射の相対 S 図式へ代入する。
方針：既存の供給変換へ公開定理を渡し、全多次数の図式と零段比較を具体化する。
規約：新しい供給仮定を残さず、相対実現後の群比較は別途証明する。
使われ方：一般共終性の相対 S• 比較の実入力。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の完備化射の wide 供給は Sp-7 により実際に成立する。
方針：一般定理を標準模型の供給変換へ直接渡す。
規約：追加の instance 仮定や一般共終性の仮定を置かない。
使われ方：条件付き相対旗 API の供給引数を消去する。 -/
theorem stableWideCofinalitySupply : StableWideCofinalitySupply.{u} :=
  stableWideCofinalitySupply_of_api
    LocalizingInvariants.idempotentCompletion_cofiberWide_discrete

/-- 概要：指定完備化射の相対旗を全 S 多次数と旗方向で具体化する。
方針：Sp-7 の実供給を全多単体的な旗図式へ代入する。
規約：供給の存在を追加の仮定に残さない。
使われ方：相対 S• の実現前の入力。 -/
def completionRelativeFlagDiagram (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u}) :=
  suppliedMultiRelativeFlagDiagram stableWideCofinalitySupply r f hf

/-- 概要：同じ全多次数の相対旗の零段は元の未置換反復 S に同型。
方針：実供給を未置換零段比較へ代入する。
規約：亜群化・Kan 置換後の零段を代用しない。
使われ方：元の K 射へ戻る実現前の比較。 -/
def completionRelativeFlagZeroIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    ((completionRelativeFlagDiagram r f hf).obj ι).obj (Opposite.op ⦋0⦌) ≅
      (((multiSEndofunctor r).obj ι).obj Y).carrier :=
  multiRelativeFlagZeroIso stableWideCofinalitySupply r ι f hf

/-- 概要：同じ全多次数の wide 亜群化の全正次数は実供給により自明。
方針：Sp-7 を代入した供給値の離散性を使用する。
規約：core 相対旗の実現の離散性とはまだ同一視しない。
使われ方：相対実現比較の障害側の入力。 -/
theorem completionMultiWide_positive_subsingleton (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      ((multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex : SSet.{u})) _⦋0⦌)
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      ((multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex : SSet.{u})) n x) :=
  multiWideStageData_discrete stableWideCofinalitySupply r ι f hf x n hn

end SerrePositivity.KST.SConstruction.Cofinality
