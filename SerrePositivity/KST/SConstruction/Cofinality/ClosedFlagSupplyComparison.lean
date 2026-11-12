module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeHeadComparison
public import SerrePositivity.KST.Fibration.Relative.ClosedStableFlags

/-!
概要：採用済み K-B2-S1 の閉じた安定旗へ元の本質像を代入する。
方針：標準単体の全体持ち上げと元の単体の部分複体所属を Yoneda で照合する。
規約：公開済みの旗定義だけを使い、未到着の相対 fiber を結論しない。
使われ方：元の相対旗と供給側 R_P の未置換の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の標準単体の旗の全体持ち上げは同じ元の単体の所属と同値。
方針：Yoneda の元の単体を部分複体へ持ち上げて全旗を回収する。
規約：頂点ごとの独立な持ち上げへ弱めない。
使われ方：K-B2-S1 の元の W 旗条件との照合。 -/
lemma completionFlagLift_iff_simplex_mem (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    (Y : StableModel.{u})
    (M : (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex) (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj (((multiSEndofunctor r).obj ι).obj Y).carrier) _⦋0⦌) :
    multiRelativeFlagPredicate r ι Y M (stdSimplex.obj n) v ↔
      Fibration.simplexVertexValue n v ∈ M.obj (Opposite.op n) := by
  constructor
  · rintro ⟨g, rfl⟩
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ M.ι))) ∈ _
    have he := congrArg SSet.yonedaEquiv
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply (g ≫ M.ι))
    exact (congrArg (fun t => t ∈ M.obj (Opposite.op n)) he).mpr
      (SSet.yonedaEquiv g).property
  · intro hv
    let t : (M : SSet.{u}) _⦋n.len⦌ := ⟨Fibration.simplexVertexValue n v, hv⟩
    let g : stdSimplex.obj n ⟶ (M : SSet.{u}) := SSet.yonedaEquiv.symm t
    refine ⟨g, ?_⟩
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm.injective
    change g ≫ M.ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm v
    apply SSet.yonedaEquiv.injective
    exact congrArg Subtype.val (SSet.yonedaEquiv.apply_symm_apply t)

/-- 概要：本質像を代入した供給側の閉じた旗条件は元の相対旗条件に一致する。
方針：供給側の全辺条件と選択した wide 模型の元の全辺模型との等号を使う。
規約：元の指定射の本質像を retract 閉包へ拡大しない。
使われ方：K-B2-S1 の R_P と元の相対 core 旗の照合。 -/
lemma completionClosedFlagPredicate_iff (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj (((multiSEndofunctor r).obj ι).obj Y).carrier) _⦋0⦌) :
    (Fibration.Relative.closedFlagStablePredicate
      (completionImageClosedPredicate r ι f hf) n).predicate v ↔
      multiRelativeFlagPredicate r ι Y
        (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex
        (stdSimplex.obj n) v := by
  rw [Fibration.Relative.closedFlagStablePredicate_iff]
  change Fibration.simplexVertexValue n v ∈
    (LocalizingInvariants.completionCofiberWide (((multiSEndofunctor r).obj ι).map f).val).obj
      (Opposite.op n) ↔ _
  rw [← completionMultiWide_eq r ι f hf]
  exact (completionFlagLift_iff_simplex_mem r ι Y _ n v).symm

end SerrePositivity.KST.SConstruction.Cofinality
