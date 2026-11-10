module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactArrowGenerators
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ArrowCardinals

/-!
概要：元の全生成辺を含む、小さい compact 射の全部分候補を存在入力なしで構成する。
方針：共通の正則濃度と元の射の compact 持ち上げを、小模型の全射性へ代入する。
規約：元の全生成辺との射圏内の同型を保持し、全射の生成性は引き続き未証明。
使われ方：P-1 f2、HTT 5.5.4.14 の最小強飽和類との比較の出発点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 全生成辺は、元の飽和射圏内で compact な小さい全部分候補の像と射圏内で同型。 -/
lemma exists_generatorContainingCompactArrowCandidates (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ IsKappaAccessible μ C ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ generatedArrowCategory edges,
          IsFullyFaithful i ∧
          (∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (i.app _ (ULift.up a))) ∧
          ∀ j : I, ∃ a : A _⦋0⦌, Nonempty (VertexIso
            ((i ≫ generatedArrowInclusion edges).app _ (ULift.up a))
            (generatorArrowVertex edges j)) := by
  obtain ⟨μ, hμ, hσ, hCμ, hAμ, hgen, _⟩ :=
    exists_regular_generatorArrowCardinal hC edges σ
  obtain ⟨A, hA, i, hi, hcompact, hcover⟩ :=
    exists_smallCompactArrowCandidates hC.hasSmallColimits hAμ edges
  have := hA
  refine ⟨μ, hμ, hσ, hCμ, A, hA, i, hi, hcompact, ?_⟩
  intro j
  have hs : arrowVertexEdge (generatorArrowVertex edges j) ∈ generatedEdges edges := by
    rw [generatorArrowVertex_edge]
    exact subset_stronglySaturatedClosure _ _ (Set.mem_range_self j)
  let f := compactGeneratedArrowVertex μ edges (generatorArrowVertex edges j) (hgen j) hs
  obtain ⟨a, ⟨ea⟩⟩ := hcover f
  exact ⟨a, ⟨(hoFunctor.map (generatedArrowInclusion edges)).toFunctor.mapIso ea⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
