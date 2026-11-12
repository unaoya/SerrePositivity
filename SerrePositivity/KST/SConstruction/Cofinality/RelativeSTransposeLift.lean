module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeSTransposeWide

/-!
概要：元の相対旗の S 転置を同じ次段の相対旗へ持ち上げる。
方針：全 Ar 評価で確認した wide 条件を元の全体持ち上げ条件へ戻す。
規約：元の包含後の射を厳密に回収する。
使われ方：相対旗の S 交換同型の順射。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の相対 S 転置は次段の元の相対旗条件を満たす。
方針：全辺 wide 所属から元の選択模型への旗全体の持ち上げを回収する。
規約：全高次単体の ambient 射を変更しない。
使われ方：全部分複体への順射の定義。 -/
lemma completionRelativeSTranspose_relative (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (v : (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier _⦋0⦌) :
    multiRelativeFlagPredicate (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι) Y
      (multiWideStageData stableWideCofinalitySupply (r + 1)
        (Fin.cons (Opposite.op ⦋m⦌) ι) f hf).subcomplex (stdSimplex.obj n)
      ((completionRelativeSTransposeDiagram r ι f hf m n).app (Opposite.op ⦋0⦌) v) := by
  apply (completionFlagLift_iff_simplex_mem (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
    Y _ n _).mpr
  rw [completionMultiWide_eq (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι) f hf]
  exact completionRelativeSTranspose_wide r ι f hf m n v

/-- 概要：元の相対旗の S 構成から同じ次段の相対旗への順射。
方針：元の転置を一致する全体旗条件で持ち上げる。
規約：元の全多次数と未置換の射を保持する。
使われ方：相対 fiber 供給の右項の元の S 図式への交換。 -/
def completionRelativeSTranspose (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier ⟶
      (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
        f hf n).carrier :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (completionRelativeSTransposeDiagram r ι f hf m n)
    (completionRelativeSTranspose_relative r ι f hf m n)

/-- 概要：元の相対 S 転置は包含後に元の ambient 転置を回収する。
方針：全部分複体への持ち上げの包含公式を使う。
規約：元の全単体の射の等号。
使われ方：逆向きの転置と元の構造射の照合。 -/
lemma completionRelativeSTranspose_inclusion (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    completionRelativeSTranspose r ι f hf m n ≫
      (completionRelativeFlagAmbientMap (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι) f hf n).val =
        completionRelativeSTransposeDiagram r ι f hf m n := rfl

end SerrePositivity.KST.SConstruction.Cofinality
