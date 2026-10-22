module

public import SerrePositivity.InfinityCategories.F2.Compact.CompactIndCompletion
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletenessUniverse

/-!
概要：冪等完備な小さい C は Indκ(C) の元の κ-compact 部分と同値。
方針：N の実際の Yoneda retract 回収を、元の C の冪等完備性で像へ戻す。
規約：正則 κ と同じ全 Yoneda を保持。使われ方：F2N-5(c) の compact 生成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]

/-- 冪等完備な C の元の compact Ind-Yoneda は本質全射。 -/
lemma compactYoneda_isEssentiallySurjective (hC : Idempotent.IsIdempotentComplete C) :
    IsEssentiallySurjective (Compact.compactIndYoneda κ C) := by
  intro y
  obtain ⟨x, hx⟩ := Compact.compactInd_retract_yoneda κ y
  obtain ⟨a, ⟨e⟩⟩ := hC.ulift.retract_iso_in_image
    (Compact.compactIndYoneda κ C) (Compact.compactIndYoneda_isFullyFaithful κ)
    (ULift.up x) y hx.some
  exact ⟨a, ⟨e.symm⟩⟩

/-- 元の全 compact Yoneda 自身が冪等完備 C と compact Indκ(C) の同値。 -/
lemma compactYoneda_isQCatEquivalence (hC : Idempotent.IsIdempotentComplete C) :
    IsQCatEquivalence (Compact.compactIndYoneda κ C) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (Compact.compactIndYoneda_isFullyFaithful κ) (compactYoneda_isEssentiallySurjective κ hC)

/-- 冪等完備な C の宇宙持ち上げと Indκ(C) の κ-compact 部分の実同値。 -/
def compactGenerationEquivalence (hC : Idempotent.IsIdempotentComplete C) :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj C)
      (Compact.kappaCompactObjects.{u, u + 1} κ (IndInfinity κ C)) :=
  (compactYoneda_isQCatEquivalence κ hC).choose

/-- 同値の順射は元の同じ compact Yoneda。 -/
lemma compactGenerationEquivalence_hom (hC : Idempotent.IsIdempotentComplete C) :
    (compactGenerationEquivalence κ hC).hom = Compact.compactIndYoneda κ C := rfl

/-- 任意の元の Ind 頂点は、元の C の対象の小さい κ-filtered 余極限。 -/
lemma indVertex_has_filteredYonedaPresentation (x : (IndInfinity κ C) _⦋0⦌) :
    ∃ (I : SSet.{u}) (hI : Quasicategory I),
      letI := hI
      IsKappaFiltered κ I ∧ ∃ a : I ⟶ C,
        ∃ c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ indYoneda κ C),
          c.vertex = x ∧ IsColimitCone c := by
  refine ⟨smallRightUnstraightening (indVertexPresheaf κ x), inferInstance,
    indVertexElements_isKappaFiltered κ x,
    smallRightUnstraighteningProjection (indVertexPresheaf κ x),
    indVertexDensityCocone κ x, indVertexDensityCocone_vertex κ x,
    indVertexDensityCocone_isColimit κ x⟩

end SerrePositivity.InfinityCategories.F2.Ind
