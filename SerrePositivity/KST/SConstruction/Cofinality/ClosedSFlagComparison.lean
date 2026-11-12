module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeSInterchange
public import SerrePositivity.KST.Fibration.Relative.ClosedFlagFunctor

/-!
概要：供給側の閉じた相対旗の S 構成を元の次段の相対旗へ同型で写す。
方針：元の包含を保つ安定模型同型に S を適用し、元の相対 S 交換へ接続する。
規約：相対 fiber の本体やその全旗自然性を追加仮定にしない。
使われ方：K-B2-S1 の右項と元の相対先頭実現の全次数照合。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：供給側 R_P の S_m と元の次段の相対旗の厳密な同型。
方針：同じ元の安定模型同型の S 像と元の相対旗交換を合成する。
規約：元の全単体と元の指定完備化射を保持する。
使われ方：供給側 core S 実現の元の相対先頭実現への比較。 -/
def completionClosedSFlagIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    (sStableModel m (Fibration.Relative.closedFlagModel
      (completionImageClosedPredicate r ι f hf) n)).carrier ≅
        (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
          f hf n).carrier :=
  stableModelForget.mapIso ((sEndofunctor m).mapIso
    (completionClosedFlagStableIso r ι f hf n)) ≪≫
      completionRelativeSInterchangeIso r ι f hf m n

end SerrePositivity.KST.SConstruction.Cofinality
