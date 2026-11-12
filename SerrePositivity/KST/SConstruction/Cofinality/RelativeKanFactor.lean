module
public import SerrePositivity.KST.SConstruction.Cofinality.KanPullbackCofinalityInput

/-!
概要：元の相対 Kan 四角形の右辺の分解の全空間は可縮である。
方針：元の可縮な核から分解単位の局所化可逆性で一点射を移す。
規約：引き戻し比較と同じ指定分解を使う。
使われ方：Sp-8 (3) の可縮な角の入力への代入。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel

open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 概要：元の相対 Kan 四角形の右辺の指定分解の全空間。
方針：実引き戻しと同じ arrow の分解を使う。
規約：置換を選び直さない。
使われ方：元の第一射影への Sp-8 (3) の代入。 -/
def completionRelativeKanFactor (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) : SSet.{u} :=
  AnodyneKanReplacement.factorization.Z.obj (Arrow.mk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedKernelRealizationPost
      (completionImageClosedPredicate r ι f hf))))

/-- 概要：元の右辺分解の全空間は Kan。
方針：同じ右因子の horn RLP と底の Ex∞ の Kan 性を使う。
規約：モデル圏の instance を追加引数にしない。
使われ方：分解後の全ホモトピーの検査。 -/
instance completionRelativeKanFactor_kanComplex (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    KanComplex (completionRelativeKanFactor r ι f hf) := by
  let a := Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedKernelRealizationPost
    (completionImageClosedPredicate r ι f hf)))
  let p := AnodyneKanReplacement.factorization.p.app a
  have hp : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr
    (AnodyneKanReplacement.factorization.hp a)
  exact @isFibrant_of_fibration SSet.{u} _ _ _ _ _ _ p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _)

/-- 概要：元の右辺分解の全空間の一点射は局所化同型。
方針：元の核の一点射から分解単位を消去する。
規約：相対 fiber の全旗自然性は不要。
使われ方：分解後の全基点の可縮性。 -/
lemma completionRelativeKanFactor_toPoint_isIso (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (completionRelativeKanFactor r ι f hf))) := by
  let a := Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedKernelRealizationPost
    (completionImageClosedPredicate r ι f hf)))
  let i := AnodyneKanReplacement.factorization.i.app a
  let Q := AnodyneHomotopy.anodyneQ
  have hi : IsIso (Q.map i) := Localization.inverts Q anodyneExtensions i
    (AnodyneKanReplacement.factorization.hi a)
  have hE := completionClosedKernelExInfinity_toPoint_isIso r ι f hf
  have he : i ≫ toUnit (completionRelativeKanFactor r ι f hf) = toUnit a.left :=
    isTerminalTensorUnit.hom_ext _ _
  have hh : IsIso (Q.map i ≫ Q.map (toUnit (completionRelativeKanFactor r ι f hf))) :=
    ((Q.map_comp _ _).symm.trans (congrArg Q.map he)).symm ▸ hE
  exact (@isIso_comp_left_iff _ _ _ _ _ (Q.map i)
    (Q.map (toUnit (completionRelativeKanFactor r ι f hf))) hi).mp hh

/-- 概要：元の右辺分解の全空間の全基点ホモトピーは一意。
方針：同じ一点射の局所化比較へ実証明を代入する。
規約：零次を含む全次数と任意の基点。
使われ方：Sp-8 (3) の可縮な角への実入力。 -/
lemma completionRelativeKanFactor_homotopy_subsingleton (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : ℕ)
    (x : (completionRelativeKanFactor r ι f hf) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (completionRelativeKanFactor r ι f hf) n x) :=
  Fibration.kanHomotopy_subsingleton_of_toPoint_localized_isIso _
    (completionRelativeKanFactor_toPoint_isIso r ι f hf) n x

end SerrePositivity.KST.SConstruction.Cofinality
