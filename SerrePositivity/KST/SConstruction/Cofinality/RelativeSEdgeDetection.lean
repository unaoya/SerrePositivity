module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagSTranspose
public import SerrePositivity.KST.SConstruction.Cofinality.CompletionImageSComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberFunctorMapping

/-!
概要：同じ指定射の S 構成の分母辺を全 Ar 評価で検出する。
方針：同じ実 cofiber の全評価と本質像の S 交換条件を使う。
規約：cofiber の同型類を各成分で独立に選び直さない。
使われ方：元の相対 S 旗の転置の全分母条件。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の反復 S 射の次段の分母辺は全 Ar 評価の分母条件と同値。
方針：元の実 cofiber を評価し、S 本質像条件の全成分判定を適用する。
規約：同じ元の指定射と全多次数を保持する。
使われ方：相対旗の S 交換の全辺条件の照合。 -/
lemma completionSWideEdge_iff_pointwise (m r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {x y : (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier _⦋0⦌}
    (s : Truncated.Edge
      (X := (truncation 2).obj
        (sStableModel m (((multiSEndofunctor r).obj ι).obj Y)).carrier) x y) :
    s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
        ((sEndofunctor m).map (((multiSEndofunctor r).obj ι).map f)).val) ↔
      ∀ a : (arNerve m) _⦋0⦌,
        (s.map ((truncation 2).map (sStableEvaluation m
          (((multiSEndofunctor r).obj ι).obj Y) a).val)).edge ∈
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
            (((multiSEndofunctor r).obj ι).map f).val) := by
  let P := completionImageClosedPredicate r ι f hf
  let Pm := completionImageClosedPredicate (r + 1) (Fin.cons (Opposite.op ⦋m⦌) ι) f hf
  let q := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare s
  have hP : Pm.predicate q.cofiber ↔ (sClosedPredicate m P).predicate q.cofiber :=
    (completionImage_sClosedPredicate_iff m r ι f hf q.cofiber).symm
  change s.edge ∈ Fibration.Relative.closedStableEdges Pm ↔
    ∀ a : (arNerve m) _⦋0⦌,
      (s.map ((truncation 2).map (sStableEvaluation m
        (((multiSEndofunctor r).obj ι).obj Y) a).val)).edge ∈
          Fibration.Relative.closedStableEdges P
  apply (Fibration.Relative.closedStableEdges_iff_cofiber Pm q).trans
  apply hP.trans
  apply forall_congr'
  intro a
  let E := sStableEvaluation m (((multiSEndofunctor r).obj ι).obj Y) a
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor E.val := stableModelHom_exact E
  exact (Fibration.Relative.closedStableEdges_iff_cofiber P (q.map E.val)).symm

end SerrePositivity.KST.SConstruction.Cofinality
