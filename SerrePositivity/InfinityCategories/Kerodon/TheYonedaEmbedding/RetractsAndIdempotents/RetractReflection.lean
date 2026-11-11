module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.RetractClosure

/-!
概要：充満忠実な元の関手は、指定した二頂点の retract を反映する。
方針：ホモトピー圏の元の二射を逆像へ移し、同じ分裂等式を忠実性で戻す。
規約：これは coherent な分裂空間の可縮性とは別の、retract の所属判定。
使われ方：Idem(C) 自身の内部での元の Yoneda 像の retract 条件。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の充満忠実な関手は、同じ指定二頂点の retract データを反映する。 -/
def VertexRetraction.ofFullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {x y : X _⦋0⦌} (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction
      (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction x y := by
  let i := Classical.choose ((hf.homotopyCategoryMap_bijective x y).surjective r.i)
  have hi := Classical.choose_spec ((hf.homotopyCategoryMap_bijective x y).surjective r.i)
  let p := Classical.choose ((hf.homotopyCategoryMap_bijective y x).surjective r.r)
  have hp := Classical.choose_spec ((hf.homotopyCategoryMap_bijective y x).surjective r.r)
  refine ⟨i, p, ?_⟩
  apply (hf.homotopyCategoryMap_bijective x x).injective
  exact ((hoFunctor.map f).toFunctor.map_comp i p).trans
    ((congrArg₂ (· ≫ ·) hi hp).trans
      (r.retract.trans ((hoFunctor.map f).toFunctor.map_id (HomotopyCategory.mk x)).symm))

/-- 元の充満忠実な関手は、同じ二頂点の retract の存在を保存・反映する。 -/
lemma isVertexRetractOf_iff_map_of_fullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    (x y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf
      (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) :=
  ⟨fun h ↦ h.map f, fun ⟨r⟩ ↦ ⟨r.ofFullyFaithful f hf⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
