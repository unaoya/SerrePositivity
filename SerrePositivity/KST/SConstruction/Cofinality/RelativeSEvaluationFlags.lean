module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeSTransposeLift

/-!
概要：次段の元の相対旗の全 Ar 評価は前段の元の相対旗となる。
方針：元の全体旗の wide 所属を全成分へ送り、Yoneda で旗全体へ戻す。
規約：元の評価関手と元の全体持ち上げ条件を保持する。
使われ方：相対旗の S 交換の逆転置の持ち上げ。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：次段の元の wide 旗は全 Ar 評価後も前段の元の相対旗。
方針：元の単体の全成分 wide 判定と元の関手頂点の Yoneda 計算を合成する。
規約：同じ旗の後合成を使い、別の代表を選ばない。
使われ方：逆向き転置の全 Ar 頂点の所属。 -/
lemma completionRelativeSFlag_evaluation (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (v : (completionRelativeFlagStableModel (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι)
      f hf n).carrier _⦋0⦌) (a : (arNerve m) _⦋0⦌) :
    multiRelativeFlagPredicate r ι Y
      (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex (stdSimplex.obj n)
      (((ihom (stdSimplex.obj n)).map
        (sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a).val).app
          (Opposite.op ⦋0⦌) v.val) := by
  let E := (sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a).val
  have hv := (completionFlagLift_iff_simplex_mem (r + 1)
    (Fin.cons (Opposite.op ⦋m⦌) ι) Y _ n v.val).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)
  have hc := (congrArg (fun M => Fibration.simplexVertexValue n v.val ∈
    M.obj (Opposite.op n))
      (completionMultiWide_eq (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι) f hf)).mp hv
  have ha := (completionSWideSimplex_iff_pointwise m r ι f hf n _).mp hc a
  apply (completionFlagLift_iff_simplex_mem r ι Y _ n _).mpr
  apply (congrArg (fun M => Fibration.simplexVertexValue n
    (((ihom (stdSimplex.obj n)).map E).app (Opposite.op ⦋0⦌) v.val) ∈
      M.obj (Opposite.op n)) (completionMultiWide_eq r ι f hf)).mpr
  have he : Fibration.simplexVertexValue n
      (((ihom (stdSimplex.obj n)).map E).app (Opposite.op ⦋0⦌) v.val) =
        E.app (Opposite.op n) (Fibration.simplexVertexValue n v.val) := by
    generalize v.val = w
    obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) _).surjective w
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ E))) =
      E.app (Opposite.op n)
        (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)))
    exact (congrArg SSet.yonedaEquiv
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply (g ≫ E))).trans
        (congrArg (fun h => E.app (Opposite.op n) (SSet.yonedaEquiv h))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply g)).symm
  exact (congrArg (fun t => t ∈ (LocalizingInvariants.completionCofiberWide
    (((multiSEndofunctor r).obj ι).map f).val).obj (Opposite.op n)) he).mpr ha

end SerrePositivity.KST.SConstruction.Cofinality
