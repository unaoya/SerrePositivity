module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactArrows
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedArrowColimits

/-!
概要：飽和射圏内の compact な小さい全部分生成候補を、元の包含と共に構成する。
方針：周囲で compact な射の小模型を、余極限保存の全部分包含で飽和射圏へ戻す。
規約：候補の compact 性と全 compact 射の被覆を証明するが、全射の生成性は未主張。
使われ方：P-1 f2、compact 生成候補からの Ind 比較の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 周囲の全射圏の compact 射は、元の飽和射圏内でも compact。 -/
lemma compactGeneratedArrowInclusion_compact {κ : Cardinal.{u}}
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (edges : I → C _⦋1⦌)
    (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactGeneratedArrows κ edges) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactGeneratedArrowInclusion κ edges).app _ f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrow_isKappaCompact_of_image hC edges
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex f.val

/-- 小さい compact 全部分候補は、閉包内の全ての周囲で compact な射を代表する。 -/
lemma exists_smallCompactArrowCandidates {κ : Cardinal.{u}}
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ ((ihom (Δ[1] : SSet.{u + 1})).obj C))
    (edges : I → C _⦋1⦌) :
    ∃ (A : SSet.{u}) (hA' : Quasicategory A),
      letI := hA'
      ∃ i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i ∧
        (∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
          (i.app _ (ULift.up a))) ∧
        ∀ f : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactGeneratedArrows κ edges) _⦋0⦌, ∃ a : A _⦋0⦌,
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (i.app _ (ULift.up a))
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactGeneratedArrowInclusion κ edges).app _ f)) := by
  obtain ⟨A, hA', ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallCompactGeneratedArrowModel hA edges
  have := hA'
  let i := e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactGeneratedArrowInclusion κ edges
  refine ⟨A, hA', i, e.isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactGeneratedArrowInclusion_isFullyFaithful κ edges), ?_, ?_⟩
  · intro a
    exact compactGeneratedArrowInclusion_compact hC edges (e.hom.app _ (ULift.up a))
  · intro f
    obtain ⟨a, ⟨ea⟩⟩ := e.isEssentiallySurjective f
    exact ⟨a.down, ⟨(hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactGeneratedArrowInclusion κ edges)).toFunctor.mapIso ea⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
