module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagDiagramIso

/-!
概要：供給側の相対実現を元の相対先頭実現へ厳密な同型で接続する。
方針：元の二重自然同型を core と対角へ写し、旗方向と S 方向の交換を照合する。
規約：元の三方向の全対角を保持する。
使われ方：相対 fiber の右項への無条件な高次消滅の供給。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の先頭 S・旗・core の全図式。
方針：元の全旗図式の全方向を保持したまま core を取る。
規約：S 方向を外側、旗方向を内側とする。
使われ方：元の二つの実現順序の照合。 -/
def completionRelativeCoreHeadDiagram (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    SimplexCategoryᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u}) :=
  completionCokernelHeadIndex r ι ⋙ completionRelativeFlagDiagram (r + 1) f hf ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：元の相対実現の二つの対角順序は同じ元の対角で同型。
方針：各次数で恒等とし、二方向の構造射の自然性を内部次数へ評価する。
規約：元の先頭 S・旗・core の三方向を保持する。
使われ方：供給側の旗を外側とする実現から元の先頭実現への接続。 -/
def completionRelativeHeadFlipIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    simplicialDiagonalFunctor.obj
      ((completionRelativeCoreHeadDiagram r ι f hf).flip ⋙ simplicialDiagonalFunctor) ≅
        completionRelativeHeadRealization r ι f hf :=
  NatIso.ofComponents (fun n => Iso.refl _) (by
    intro n k θ
    let A := completionRelativeCoreHeadDiagram r ι f hf
    change (((A.obj n).map θ).app n ≫ ((A.map θ).app k).app n ≫
      ((A.obj k).obj k).map θ) ≫ 𝟙 _ =
        𝟙 _ ≫ (((A.map θ).app n).app n ≫ ((A.obj k).map θ).app n ≫
          ((A.obj k).obj k).map θ)
    simp only [Category.comp_id, Category.id_comp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h.app n ≫ ((A.obj k).obj k).map θ)
        ((A.map θ).naturality θ)).trans (Category.assoc _ _ _)))

/-- 概要：供給側 R_P の元の相対実現と元の相対先頭実現の同型。
方針：元の二重 S 交換自然同型を core・対角へ送り、二つの対角順序を交換する。
規約：元の本質像・元の包含・未置換の全実現を使う。
使われ方：K-B2-S1 の右項の高次消滅の消費。 -/
def completionClosedRelativeRealizationIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    Fibration.Relative.closedRelativeRealization (completionImageClosedPredicate r ι f hf) ≅
      completionRelativeHeadRealization r ι f hf :=
  simplicialDiagonalFunctor.mapIso
    (Functor.isoWhiskerRight (completionClosedSFlagDiagramIso r ι f hf)
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor ⋙ simplicialDiagonalFunctor)) ≪≫
          completionRelativeHeadFlipIso r ι f hf

end SerrePositivity.KST.SConstruction.Cofinality
