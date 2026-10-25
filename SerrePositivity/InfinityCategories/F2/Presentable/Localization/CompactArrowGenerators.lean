module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactArrows
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedArrowColimits

/-!
概要：飽和射圏内の compact な小さい全部分生成候補を、元の包含と共に構成する。
方針：周囲で compact な射の小模型を、余極限保存の全部分包含で飽和射圏へ戻す。
規約：候補の compact 性と全 compact 射の被覆を証明するが、全射の生成性は未主張。
使われ方：P-1 f2、compact 生成候補からの Ind 比較の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 周囲の全射圏の compact 射は、元の飽和射圏内でも compact。 -/
lemma compactGeneratedArrowInclusion_compact {κ : Cardinal.{u}}
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌)
    (f : (compactGeneratedArrows κ edges) _⦋0⦌) :
    Compact.IsKappaCompact.{u, u + 1} κ
      ((compactGeneratedArrowInclusion κ edges).app _ f) := by
  apply generatedArrow_isKappaCompact_of_image hC edges
  exact fullSubcomplexOnVertices_vertex f.val

/-- 小さい compact 全部分候補は、閉包内の全ての周囲で compact な射を代表する。 -/
lemma exists_smallCompactArrowCandidates {κ : Cardinal.{u}}
    (hC : HasSmallColimits C)
    (hA : IsKappaAccessible κ ((ihom (Δ[1] : SSet.{u + 1})).obj C))
    (edges : I → C _⦋1⦌) :
    ∃ (A : SSet.{u}) (hA' : Quasicategory A),
      letI := hA'
      ∃ i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ generatedArrowCategory edges,
        IsFullyFaithful i ∧
        (∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ
          (i.app _ (ULift.up a))) ∧
        ∀ f : (compactGeneratedArrows κ edges) _⦋0⦌, ∃ a : A _⦋0⦌,
          Nonempty (VertexIso (i.app _ (ULift.up a))
            ((compactGeneratedArrowInclusion κ edges).app _ f)) := by
  obtain ⟨A, hA', ⟨e⟩⟩ := exists_smallCompactGeneratedArrowModel hA edges
  have := hA'
  let i := e.hom ≫ compactGeneratedArrowInclusion κ edges
  refine ⟨A, hA', i, e.isFullyFaithful.comp
    (compactGeneratedArrowInclusion_isFullyFaithful κ edges), ?_, ?_⟩
  · intro a
    exact compactGeneratedArrowInclusion_compact hC edges (e.hom.app _ (ULift.up a))
  · intro f
    obtain ⟨a, ⟨ea⟩⟩ := e.isEssentiallySurjective f
    exact ⟨a.down, ⟨(hoFunctor.map (compactGeneratedArrowInclusion κ edges)).toFunctor.mapIso ea⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
