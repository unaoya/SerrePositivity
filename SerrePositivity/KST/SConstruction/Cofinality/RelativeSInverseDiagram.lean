module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeSEvaluationFlags

/-!
概要：次段の元の相対旗を前段の元の相対旗値の Ar 図式へ逆転置する。
方針：元の全 Ar 評価の所属を使い、全部分圏の内部 Hom へ族全体を持ち上げる。
規約：元の全部分旗包含と全自然変換を保持する。
使われ方：相対旗の S 交換の逆射の gapped 条件。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：次段の元の相対旗の二重内部 Hom への逆転置。
方針：元の包含と S 図式包含の後に内部 Hom の二方向を交換する。
規約：前段の全部分旗への持ち上げは後続で行う。
使われ方：逆射の元の ambient 図式。 -/
def completionRelativeSRawInverse (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
      f hf n).carrier ⟶
      (ihom (arNerve m)).obj ((ihom (stdSimplex.obj n)).obj
        (((multiSEndofunctor r).obj ι).obj Y).carrier) :=
  (completionRelativeFlagAmbientMap (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι) f hf n).val ≫
    (ihom (stdSimplex.obj n)).map
      (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (stdSimplex.obj n) (arNerve m)
          (((multiSEndofunctor r).obj ι).obj Y).carrier).hom

/-- 概要：逆転置の元の頂点は元の S 値の旗の実際の転置。
方針：元の関手頂点の表示を内部 Hom の交換へ渡す。
規約：元の旗の全体を転置する。
使われ方：逆転置の各 Ar 成分の所属判定。 -/
lemma completionRelativeSRawInverse_vertex (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (v : (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
      f hf n).carrier _⦋0⦌) :
    (completionRelativeSRawInverse r ι f hf m n).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (stdSimplex.obj n) (arNerve m)
        (((multiSEndofunctor r).obj ι).obj Y).carrier
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n)
          (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier).symm v.val ≫
            (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι)) := by
  let g := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n)
    (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier).symm v.val
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply v.val
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (stdSimplex.obj n) (arNerve m)
    (((multiSEndofunctor r).obj ι).obj Y).carrier).hom.app (Opposite.op ⦋0⦌)
      (((ihom (stdSimplex.obj n)).map
        (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι).app
          (Opposite.op ⦋0⦌) v.val) = _
  have h := congrArg (fun w : ((ihom (stdSimplex.obj n)).obj
      (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier) _⦋0⦌ =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (stdSimplex.obj n) (arNerve m)
      (((multiSEndofunctor r).obj ι).obj Y).carrier).hom.app (Opposite.op ⦋0⦌)
        (((ihom (stdSimplex.obj n)).map
          (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι).app
            (Opposite.op ⦋0⦌) w)) hv.symm
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex (stdSimplex.obj n) (arNerve m)
    (((multiSEndofunctor r).obj ι).obj Y).carrier
    (g ≫ (gappedSubcomplex m (((multiSEndofunctor r).obj ι).obj Y).carrier).ι))

/-- 概要：逆転置の全 Ar 成分は前段の元の相対旗である。
方針：元の全体旗の全評価の所属判定を転置の頂点公式へ適用する。
規約：元の ambient 全自然変換を制限しない。
使われ方：全部分旗値の内部 Hom への持ち上げ。 -/
lemma completionRelativeSRawInverse_relative (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (v : (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
      f hf n).carrier _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies (arNerve m)
      ((ihom (stdSimplex.obj n)).obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
      (multiRelativeFlagPredicate r ι Y
        (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex (stdSimplex.obj n))
      ((completionRelativeSRawInverse r ι f hf m n).app (Opposite.op ⦋0⦌) v) := by
  intro a
  rw [completionRelativeSRawInverse_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
  let E := (sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a).val
  have h := completionRelativeSFlag_evaluation r ι f hf m n v a
  have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n)
    (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier).apply_symm_apply v.val
  exact (congrArg (fun w => multiRelativeFlagPredicate r ι Y
    (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex (stdSimplex.obj n)
      (((ihom (stdSimplex.obj n)).map E).app (Opposite.op ⦋0⦌) w)) hv).mpr h

/-- 概要：元の逆転置を前段の相対旗値の Ar 図式へ持ち上げる。
方針：全部分複体の内部 Hom の元の逆比較を使う。
規約：全高次単体の族を一つの射で持ち上げる。
使われ方：逆射の gapped 条件の検証。 -/
def completionRelativeSInverseDiagram (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory) :
    (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
      f hf n).carrier ⟶
        (ihom (arNerve m)).obj (completionRelativeFlagStableModel r ι f hf n).carrier :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (completionRelativeSRawInverse r ι f hf m n)
    (completionRelativeSRawInverse_relative r ι f hf m n) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward (arNerve m)
        ((ihom (stdSimplex.obj n)).obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
        (multiRelativeFlagPredicate r ι Y
          (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex (stdSimplex.obj n))

end SerrePositivity.KST.SConstruction.Cofinality
