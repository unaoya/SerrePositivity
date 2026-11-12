module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeKanFactor

/-!
概要：Sp-8 (3) の明示入力を元の相対実引き戻しの第一射影へ代入する。
方針：同じ右辺分解と二つの角の実消滅を使う。
規約：元の指定射と同じ実引き戻し模型を保持する。
使われ方：元の包含の Kan 誘導写像へ群条件を戻す。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open SerrePositivity.KST.Comparison
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 概要：元の相対 Kan 四角形の同じ実引き戻し。
方針：元の定数旗と元の右辺で指定された分解を使う。
規約：全旗自然性が未供給でも対象は定義される。
使われ方：Sp-8 (3) の実入力。 -/
def completionRelativeKanPullback (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) : SSet.{u} :=
  homotopyPullbackObject
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedRelativeConstant
      (completionImageClosedPredicate r ι f hf)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedKernelRealizationPost
      (completionImageClosedPredicate r ι f hf)))

/-- 概要：元の相対実引き戻しは Kan。
方針：同じ第一射影の fibration 性と Ex∞ 標的の Kan 性。
規約：元の模型を保持する。
使われ方：第一射影の元のホモトピー群。 -/
instance completionRelativeKanPullback_kanComplex (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    KanComplex (completionRelativeKanPullback r ι f hf) := by
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj
      (coreSRealizationFunctor.obj (((multiSEndofunctor r).obj ι).obj Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  exact homotopyPullbackObject_kan _ _

/-- 概要：元の相対引き戻しの第一射影。
方針：同じ実引き戻しの指定第一射影を使う。
規約：元の F(B) の Ex∞ 模型への射。
使われ方：元の本質像包含の射影回収。 -/
def completionRelativeKanProjection (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionRelativeKanPullback r ι f hf ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (coreSRealizationFunctor.obj (((multiSEndofunctor r).obj ι).obj Y)) :=
  pullback.fst _ _

/-- 概要：Sp-8 (3) 入力下で元の第一射影は π₁ 単射・二次以上で全単射。
方針：元の分解の horn RLP と両角の実消滅を一般供給へ代入する。
規約：相対 fiber の全旗自然性はまだ仮定しない。
使われ方：元の包含の誘導写像への接続。 -/
lemma completionRelativeKanProjection_groupConditions_of_input
    (supply : KanPullbackCofinalityInput.{u}) (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : (completionRelativeKanPullback r ι f hf) _⦋0⦌) :
    Function.Injective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 1 (completionRelativeKanProjection r ι f hf) (x := a) rfl) ∧
      ∀ n : ℕ, 1 < n → Function.Bijective
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (completionRelativeKanProjection r ι f hf) (x := a) rfl) := by
  let P := completionImageClosedPredicate r ι f hf
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedRelativeConstant P)
  let b := Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedKernelRealizationPost P))
  let p := AnodyneKanReplacement.factorization.p.app b
  let : KanComplex (AnodyneKanReplacement.factorization.Z.obj b) :=
    completionRelativeKanFactor_kanComplex r ι f hf
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj
      (coreSRealizationFunctor.obj (((multiSEndofunctor r).obj ι).obj Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (Fibration.Relative.closedRelativeRealization P)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  exact supply (completionRelativeKanProjection r ι f hf) (pullback.snd c p) c p
    (IsPullback.of_hasPullback c p) (AnodyneKanReplacement.factorization.hp b)
    (completionRelativeKanFactor_homotopy_subsingleton r ι f hf)
    (completionClosedRelativeExInfinity_higher_subsingleton r ι f hf) a

end SerrePositivity.KST.SConstruction.Cofinality
