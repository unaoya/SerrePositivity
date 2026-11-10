module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImagePresentations

/-!
概要：元の全射圏での compact 性を保持する小模型と、その完全忠実な Ind 比較。
方針：実際の compact 小模型の同値から包含を作り、公開された分離入口で比較する。
規約：内在的な compact 性だけから周囲での compact 性を逆算しない。
使われ方：Ind 像の実表示の全項に、周囲での compact 性を供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I : Type u}

/-- 同じ実比較の Yoneda 像は周囲でも compact で、閉包内の全 compact 射を被覆する。 -/
lemma exists_ambientCompactIndComparison (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (hAr : IsKappaAccessible κ ((ihom (Δ[1] : SSet.{u + 1})).obj C))
    (edges : I → C _⦋1⦌) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      ∃ G : Ind.IndInfinity κ A ⟶ generatedArrowCategory edges,
        IsFullyFaithful G ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G ∧
        (∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ
          ((Ind.indYoneda κ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a))) ∧
        ∀ f : (compactGeneratedArrows κ edges) _⦋0⦌,
          IndArrowImageVertex edges G
            ((compactGeneratedArrowInclusion κ edges ≫ generatedArrowInclusion edges).app _ f) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := exists_smallCompactGeneratedArrowModel hAr edges
  have := hA
  let i := e.hom ≫ compactGeneratedArrowInclusion κ edges
  have hi : IsFullyFaithful i := e.isFullyFaithful.comp
    (compactGeneratedArrowInclusion_isFullyFaithful κ edges)
  have hc (a : A _⦋0⦌) : Compact.IsKappaCompact.{u, u + 1} κ (i.app _ (ULift.up a)) :=
    compactGeneratedArrowInclusion_compact hC edges (e.hom.app _ (ULift.up a))
  obtain ⟨G, hG, ⟨η⟩⟩ := exists_indComparison
    ((generatedArrow_hasSmallColimits hC edges).hasSmallKappaFilteredColimits κ) i
  refine ⟨A, hA, G, indComparison_isFullyFaithful_of_compact hi hc hG η, hG, ?_, ?_⟩
  · intro a
    have ha : Compact.IsKappaCompact.{u, u + 1} κ
        ((i ≫ generatedArrowInclusion edges).app _ (ULift.up a)) :=
      fullSubcomplexOnVertices_vertex (e.hom.app _ (ULift.up a)).val
    exact (Compact.isKappaCompact_iff_of_iso
      (VertexIso.map (FunctorIso.app η (ULift.up a)) (generatedArrowInclusion edges))).mpr ha
  · intro f
    obtain ⟨a, ⟨ha⟩⟩ := e.isEssentiallySurjective f
    exact ⟨(Ind.indYoneda κ A).app _ a,
      ⟨VertexIso.map (FunctorIso.app η a ≪≫
        VertexIso.map ha (compactGeneratedArrowInclusion κ edges))
          (generatedArrowInclusion edges)⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
