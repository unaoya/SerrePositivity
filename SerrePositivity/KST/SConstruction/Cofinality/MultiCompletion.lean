module
public import SerrePositivity.KST.SConstruction.Cofinality.CompletionStabilization
public import SerrePositivity.KST.SConstruction.FirstRowFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FunctorComplete
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessEquivalence

/-!
概要：指定された完備化射の全多次数の有限反復 S も冪等完備化となる。
方針：第一行同値で標的の完備性を移し、双積懸垂の像回収で retract 条件を作る。
規約：同じ多次数と元の完全射を保ち、亜群化の比較は別工程とする。
使われ方：Sp-7 の一般供給を全多次数の相対 S 図式へ代入する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：完備な安定標的の元の S_n は冪等完備。
方針：第一行の全関手圏の完備性を元の gapped 図式圏へ同値で移す。
規約：第一行への置換を公開対象にせず、元の S_n に結論する。
使われ方：有限反復 S の完備標的の構成。 -/
lemma sStableModel_isIdempotentComplete (n : ℕ) (Y : StableModel.{u})
    (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete Y.carrier) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (sStableModel n Y).carrier :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.functor_isIdempotentComplete (firstRowNerve n) hY).of_equivalence
    (firstRowEquivalence n Y.carrier).symm

/-- 概要：独立な全多次数の反復 S は標的の冪等完備性を保つ。
方針：各方向の第一行同値による完備性を反復する。
規約：零反復を含み、多次数を対角へ制限しない。
使われ方：全多次数の完備化証拠の第一条件。 -/
lemma multiS_isIdempotentComplete (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    (Y : StableModel.{u}) (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete Y.carrier) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (((multiSEndofunctor r).obj ι).obj Y).carrier := by
  induction r with
  | zero => exact hY
  | succ r ih =>
    exact sStableModel_isIdempotentComplete (ι 0).unop.len _
      (ih (fun i => ι i.succ))

/-- 概要：全多次数の元の反復 S 射は、元の完備化証拠から冪等完備化となる。
方針：双積懸垂への標準分裂包含を、同じ指定射の像同型と合成する。
規約：全射性や始域の完備性は仮定しない。
使われ方：一般の wide 部分圏 API へ渡す同じ多次数の実入力。 -/
theorem multiSEndofunctor_map_isIdempotentCompletion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (((multiSEndofunctor r).obj ι).map f).val := by
  refine ⟨multiS_isIdempotentComplete r ι Y hf.1,
    multiSEndofunctor_map_isFullyFaithful r ι f hf.2.1, ?_⟩
  intro y
  obtain ⟨c, ⟨e⟩⟩ := multiSBiprodShift_mem_image_of_completion r ι f hf
    (HomotopyCategory.mk y)
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective c
  refine ⟨x, ⟨?_⟩⟩
  exact {
    i := biprod.inl (C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) ≫ e.hom
    r := e.inv ≫ biprod.fst (C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
    retract := (Category.assoc _ _ _).trans
      ((congrArg (fun k => biprod.inl (C := hoFunctor.obj
        (((multiSEndofunctor r).obj ι).obj Y).carrier) ≫ k)
        (e.hom_inv_id_assoc _)).trans (biprod.inl_fst)) }

end SerrePositivity.KST.SConstruction.Cofinality
