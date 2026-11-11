module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagInclusion

/-!
概要：供給側の相対 S 交換は旗の全ての面・退化を保つ。
方針：元の全部分旗と gapped 図式の二重包含で全成分を照合する。
規約：対角だけでなく全旗次数での元の射の等号。
使われ方：同じ供給側実現と元の相対先頭実現の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の供給側 S 交換は旗方向の制限に厳密に自然。
方針：元の全高次単体を全 Ar 成分で評価して照合する。
規約：元の旗の全ての面・退化。
使われ方：元の二重実現への自然同型。 -/
lemma completionClosedSFlagIso_flag_naturality (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ)
    {n k : SimplexCategory} (θ : k ⟶ n) :
    ((sEndofunctor m).map (Fibration.Relative.closedFlagMap
      (completionImageClosedPredicate r ι f hf) θ)).val ≫
        (completionClosedSFlagIso r ι f hf m k).hom =
      (completionClosedSFlagIso r ι f hf m n).hom ≫
        suppliedMultiRelativeFlagsPrecomp stableWideCofinalitySupply (r + 1)
          (Fin.cons (Opposite.op ⦋m⦌) ι) f hf (SSet.stdSimplex.map θ) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro v
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro b
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro t β
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.KST.SConstruction.Cofinality
