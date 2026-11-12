module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagSEvaluations

/-!
概要：元の相対 S 旗の転置は同じ次段の wide 旗条件を保つ。
方針：全 Ar 評価で元の相対旗を回収し、全辺の分母条件を点ごとに判定する。
規約：元の全体旗と元の指定反復 S 射を保持する。
使われ方：元の相対旗の S 交換の順方向の持ち上げ。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：転置した元の旗の単体は全 Ar 評価で元の相対旗の単体を回収する。
方針：元の転置評価の等号を Yoneda の元の単体に適用する。
規約：新たな旗や代表を選ばない。
使われ方：転置旗の全辺の wide 条件。 -/
lemma completionRelativeSTranspose_simplex_evaluation (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (v : (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier _⦋0⦌)
    (a : (arNerve m) _⦋0⦌) :
    (sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a).val.app (Opposite.op n)
        (Fibration.simplexVertexValue n
          ((completionRelativeSTransposeDiagram r ι f hf m n).app (Opposite.op ⦋0⦌) v)) =
      Fibration.simplexVertexValue n
        (((completionRelativeFlagAmbientMap r ι f hf n).val).app (Opposite.op ⦋0⦌)
          ((sStableEvaluation m (completionRelativeFlagStableModel r ι f hf n) a).val.app
            (Opposite.op ⦋0⦌) v)) := by
  let E := (sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a).val
  let w := (completionRelativeSTransposeDiagram r ι f hf m n).app (Opposite.op ⦋0⦌) v
  have he := congrArg (fun h => h.app (Opposite.op ⦋0⦌) v)
    (completionRelativeSTransposeDiagram_evaluation r ι f hf m n a)
  have hw : E.app (Opposite.op n) (Fibration.simplexVertexValue n w) =
      Fibration.simplexVertexValue n
        (((ihom (stdSimplex.obj n)).map E).app (Opposite.op ⦋0⦌) w) := by
    generalize w = z
    obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) _).surjective z
    change E.app (Opposite.op n)
      (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))) =
        SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ E)))
    exact (congrArg (fun h => E.app (Opposite.op n) (SSet.yonedaEquiv h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply g)).trans
        (congrArg SSet.yonedaEquiv
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply (g ≫ E))).symm
  exact hw.trans (congrArg (Fibration.simplexVertexValue n) he)

/-- 概要：元の相対 S 転置の旗は同じ次段の全辺 wide 条件を満たす。
方針：各 Ar 評価で元の相対旗の所属を回収し、分母の全成分判定を戻す。
規約：元の指定射と同じ反復 S 多次数での全体旗。
使われ方：相対旗の S 交換の順方向を全部分圏へ持ち上げる。 -/
lemma completionRelativeSTranspose_wide (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (m : ℕ) (n : SimplexCategory)
    (v : (sStableModel m (completionRelativeFlagStableModel r ι f hf n)).carrier _⦋0⦌) :
    Fibration.simplexVertexValue n
        ((completionRelativeSTransposeDiagram r ι f hf m n).app (Opposite.op ⦋0⦌) v) ∈
      (LocalizingInvariants.completionCofiberWide
        ((sEndofunctor m).map (((multiSEndofunctor r).obj ι).map f)).val).obj (Opposite.op n) := by
  apply (completionSWideSimplex_iff_pointwise m r ι f hf n _).mpr
  intro a
  let z := (sStableEvaluation m (completionRelativeFlagStableModel r ι f hf n) a).val.app
    (Opposite.op ⦋0⦌) v
  have hz := (completionFlagLift_iff_simplex_mem r ι Y
    (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex n z.val).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex z)
  have hw : Fibration.simplexVertexValue n z.val ∈
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val).obj (Opposite.op n) := by
    rw [← completionMultiWide_eq r ι f hf]
    exact hz
  exact (congrArg (fun t => t ∈
    (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val).obj (Opposite.op n))
        (completionRelativeSTranspose_simplex_evaluation r ι f hf m n v a)).mpr hw

end SerrePositivity.KST.SConstruction.Cofinality
