module
public import SerrePositivity.KST.SConstruction.Cofinality.StabilizedDiagramImage
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IdempotentCompletionDensity

/-!
概要：D-22 の実補対象供給を同じ完備化射の有限反復 S に代入する。
方針：元の完全射の完全性と実完備化証拠から密度入力を充足する。
規約：新しい密度仮定を加えず、一般共終性の群比較とは区別する。
使われ方：有限反復 S の双積懸垂を元の完全射の像へ戻す。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：完備化射の S_n 上の像は同じ S_n 内の各双積懸垂を含む。
方針：D-22 の密度を元の射に適用し、一方向の有限 S 図式の回収へ渡す。
規約：元の完備化証拠以外の密度仮定を加えない。
使われ方：正反復 S• の補対象の供給。 -/
theorem sBiprodShift_mem_image_of_completion (n : ℕ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (d : hoFunctor.obj (sStableModel n Y).carrier) :
    ∃ c : hoFunctor.obj (sStableModel n X).carrier,
      Nonempty (biprod d ((shiftFunctor (hoFunctor.obj (sStableModel n Y).carrier)
        (1 : ℤ)).obj d) ≅ (hoFunctor.map ((sEndofunctor n).map f).val).toFunctor.obj c) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val := stableModelHom_exact f
  exact sBiprodShift_mem_image_of_density n f hf.2.1
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExactFunctor.biprod_shift_mem_essentialImage_of_idempotentCompletion f.val hf) d

/-- 概要：同じ完備化射の全多次数の反復 S 上の像は各双積懸垂を含む。
方針：実補対象供給を有限反復の像回収へ代入する。
規約：元の完全射と独立な全多次数を保持する。
使われ方：有限反復図式の相対比較を構成する補対象。 -/
theorem multiSBiprodShift_mem_image_of_completion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (d : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    ∃ c : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj X).carrier,
      Nonempty (biprod d ((shiftFunctor
        (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) (1 : ℤ)).obj d) ≅
          (hoFunctor.map (((multiSEndofunctor r).obj ι).map f).val).toFunctor.obj c) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val := stableModelHom_exact f
  exact multiSBiprodShift_mem_image_of_density r ι f hf.2.1
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExactFunctor.biprod_shift_mem_essentialImage_of_idempotentCompletion f.val hf) d

/-- 概要：各値が双積懸垂で表される反復 S の全パラメータ族を、同じ始域へ戻す。
方針：各値の像所属を実密度定理で充足し、全図式を一つの関手同型で回収する。
規約：異なる多次数間の自然性や厳密境界延長は別の条件。
使われ方：有限反復 S の安定化された図式の全族回収。 -/
theorem exists_multiSFamily_of_biprodShift (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {K : SSet.{u}} {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (F : K ⟶ (((multiSEndofunctor r).obj ι).obj Y).carrier)
    (hF : ∀ k : K _⦋0⦌, ∃ d : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier,
      Nonempty ((HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) k) :
        hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) ≅
        biprod (C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
          d ((shiftFunctor (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
          (1 : ℤ)).obj d))) :
    ∃ G : K ⟶ (((multiSEndofunctor r).obj ι).obj X).carrier,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ (((multiSEndofunctor r).obj ι).map f).val) F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.exists_diagram_in_fullyFaithful_source _
    (multiSEndofunctor_map_isFullyFaithful r ι f hf.2.1)
  intro k
  obtain ⟨d, ⟨ed⟩⟩ := hF k
  obtain ⟨c, ⟨ec⟩⟩ := multiSBiprodShift_mem_image_of_completion r ι f hf d
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective c
  exact ⟨x, ⟨ec.symm ≪≫ ed.symm⟩⟩

end SerrePositivity.KST.SConstruction.Cofinality
