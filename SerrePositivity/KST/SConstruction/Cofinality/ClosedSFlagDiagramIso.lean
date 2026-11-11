module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagSNaturality

/-!
概要：供給側 R_P の元の S 図式と元の相対旗の先頭図式を二重自然同型で結ぶ。
方針：元の S 交換同型を二方向の全ての面・退化に関して束ねる。
規約：core や実現を取る前の元の全図式。
使われ方：同じ供給側の相対実現と元の相対先頭実現の同型。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：供給側の閉じた相対旗の元の全 S 図式。
方針：元の単体的安定模型に元の S 自己関手を適用して底を忘れる。
規約：旗方向を外側、S 方向を内側とする。
使われ方：元の core S 実現を取る前の供給側図式。 -/
def completionClosedSFlagDiagram (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    SimplexCategoryᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u}) :=
  Fibration.Relative.closedFlagSimplicial (completionImageClosedPredicate r ι f hf) ⋙
    simplicialStableEndofunctor.flip ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ StableModel.{u} SSet.{u}).obj stableModelForget

/-- 概要：供給側と元の相対先頭図式の実現前の二重自然同型。
方針：元の交換同型と元の二方向の自然性を直接束ねる。
規約：全旗次数と全 S 次数を独立に保持する。
使われ方：相対 fiber 右項の元の実現への接続。 -/
def completionClosedSFlagDiagramIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionClosedSFlagDiagram r ι f hf ≅
      (completionCokernelHeadIndex r ι ⋙ completionRelativeFlagDiagram (r + 1) f hf).flip :=
  NatIso.ofComponents
    (fun n => NatIso.ofComponents
      (fun m => completionClosedSFlagIso r ι f hf m.unop.len n.unop)
      (fun θ => completionClosedSFlagIso_s_naturality r ι f hf n.unop θ))
    (fun θ => by
      apply NatTrans.ext
      funext m
      exact completionClosedSFlagIso_flag_naturality r ι f hf m.unop.len θ.unop)

end SerrePositivity.KST.SConstruction.Cofinality
