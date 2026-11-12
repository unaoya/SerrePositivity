module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagNaturality

/-!
概要：供給側の相対 S 交換は元の S 方向の全ての面・退化を保つ。
方針：元の二つの方向の全成分で同じ再添字を照合する。
規約：元の全多次数の構造射を保持する。
使われ方：元の相対先頭実現への二重自然同型。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の供給側 S 交換は S 方向の制限に厳密に自然。
方針：元の全高次単体の Ar 方向の制限と旗方向の評価を交換する。
規約：先頭 S 方向の全ての面・退化。
使われ方：同じ元の二重実現への自然同型。 -/
lemma completionClosedSFlagIso_s_naturality (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (t : SimplexCategory)
    {n k : SimplexCategoryᵒᵖ} (θ : n ⟶ k) :
    ((simplicialStableEndofunctor.map θ).app (Fibration.Relative.closedFlagModel
      (completionImageClosedPredicate r ι f hf) t)).val ≫
        (completionClosedSFlagIso r ι f hf k.unop.len t).hom =
      (completionClosedSFlagIso r ι f hf n.unop.len t).hom ≫
        suppliedMultiRelativeFlagsMap stableWideCofinalitySupply (r + 1)
          ((completionCokernelHeadIndex r ι).map θ) f hf (SSet.stdSimplex.obj t) := by
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
  intro z β
  apply ConcreteCategory.hom_ext
  intro a
  simp only [suppliedMultiRelativeFlagsMap, completionCokernelHead_structureMap]
  rfl

end SerrePositivity.KST.SConstruction.Cofinality
