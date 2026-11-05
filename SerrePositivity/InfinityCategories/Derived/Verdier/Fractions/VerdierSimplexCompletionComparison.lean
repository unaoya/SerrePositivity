module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Derived.KanModels.GroupoidCompletionKanComparison

/-!
概要：元の標準単体商比較を、その同じ射の亜群化評価の全写像空間で検査する。
方針：全次数の本質的全射性を core の実辺に移し、亜群化の単位で可逆性を反映する。
規約：全写像空間の充満忠実性は未放電。対象の持ち上げからは推論しない。
使われ方：c5 の元の厳密 core 逆像射影に残る正確な証明義務。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

private lemma core_vertexIso {Y : SSet.{u}} [Quasicategory Y]
    (x y : (quasicategoryCore Y : SSet.{u}) _⦋0⦌) (e : VertexIso x.val y.val) :
    Nonempty (VertexIso x y) := by
  obtain ⟨s, hs⟩ := homotopyCategory_homMk_surjective x.val y.val e.hom
  have hi : IsInvertibleEdge s := by rw [IsInvertibleEdge, hs]; infer_instance
  let t : SSet.Edge x y :=
    ⟨⟨s.edge, (quasicategoryCore_mem_edge_iff _).mpr
      ((isInvertibleEdge_congr (e := s) (f := edgeOfSimplex s.edge) rfl).mp hi)⟩,
      Subtype.ext s.src_eq, Subtype.ext s.tgt_eq⟩
  have : IsIso (Truncated.HomotopyCategory.homMk t.toTruncated) :=
    @IsGroupoid.all_isIso (hoFunctor.obj (quasicategoryCore Y : SSet.{u})) _
      (kanComplex_ho_isGroupoid _) _ _ _
  exact ⟨asIso (Truncated.HomotopyCategory.homMk t.toTruncated)⟩

/-- 本質的全射な関手の同じ core 逆像射影も、本質的に全射。 -/
lemma corePreimageProjection_isEssentiallySurjective {X Y : SSet.{u}}
    [Quasicategory Y] (f : X ⟶ Y) (hf : IsEssentiallySurjective f) :
    IsEssentiallySurjective ((quasicategoryCore Y).fromPreimage f) := by
  intro y
  obtain ⟨x, ⟨e⟩⟩ := hf y.val
  exact ⟨⟨x, quasicategoryCore_vertex (f.app (Opposite.op ⦋0⦌) x)⟩,
    core_vertexIso _ y e⟩

/-- 元の厳密 core 逆像射影の対象側は、零次を含む全次数で放電済み。 -/
lemma relativeFirstRowSimplexQuotient_isEssentiallySurjective
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (n : ℕ) :
    IsEssentiallySurjective (relativeFirstRowSimplexQuotient q n) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.corePreimageProjection_isEssentiallySurjective _
    (verdierProjectionSimplex_isEssentiallySurjective h n)

/-- 元の商射そのものを、全辺局所化の普遍性によって Kan 標的へ下ろす。 -/
def relativeFirstRowSimplexCompletionComparison {B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (relativeFirstRowSimplex q n : SSet.{u}) ⟶
      (quasicategoryCore ((ihom (Δ[n] : SSet.{u})).obj C.obj) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluation (relativeFirstRowSimplexQuotient q n)

/-- 評価は亜群化の同じ単位との合成で、元の商射を全 FunctorIso として回収する。 -/
def relativeFirstRowSimplexCompletionComparison_unitIso {B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C) (n : ℕ) :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (relativeFirstRowSimplex q n : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q n)
      (relativeFirstRowSimplexQuotient q n) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluationIso (relativeFirstRowSimplexQuotient q n)

/-- 亜群化評価にも、元の商射の対象持ち上げと同じ全同型が残る。 -/
lemma relativeFirstRowSimplexCompletionComparison_isEssentiallySurjective
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (n : ℕ) :
    IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q n) := by
  intro y
  obtain ⟨x, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexQuotient_isEssentiallySurjective h n y
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap _).app (Opposite.op ⦋0⦌) x,
    ⟨FunctorIso.app (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison_unitIso q n) x ≪≫ e⟩⟩

/-- 元の商射の局所化可逆性は、その同じ亜群化評価の可逆性と同値。 -/
lemma relativeFirstRowSimplexQuotient_localized_isIso_iff_completion
    {B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient q n)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q n)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hu := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.groupoidCompletionUnit_anodyneQ_isIso
    (relativeFirstRowSimplex q n : SSet.{u})
  have he : Q.map (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (relativeFirstRowSimplex q n : SSet.{u})) ≫
      Q.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q n) =
      Q.map (relativeFirstRowSimplexQuotient q n) := by
    rw [← Q.map_comp]
    exact AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts
      (FunctorIso.simplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison_unitIso q n))
  constructor
  · intro hp
    have hc : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap _) ≫
        Q.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q n)) := he.symm ▸ hp
    exact (isIso_comp_left_iff _ _).mp hc
  · intro hc
    exact he ▸ inferInstance

/-- c5 の元の射に残る条件は、亜群化評価の全 pinched 写像空間の同値そのもの。 -/
lemma relativeFirstRowSimplexQuotient_localized_isIso_iff_fullyFaithful
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient q n)) ↔
      IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q n) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexQuotient_localized_isIso_iff_completion]
  constructor
  · intro hc
    exact (isQCatEquivalence_of_anodyneQ_isIso _ hc).isFullyFaithful
  · intro hf
    have he := isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _ hf
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison_isEssentiallySurjective h n)
    exact homotopyEquivalence_anodyneQ_isIso _ he.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.corePreimageProjection_isEssentiallySurjective := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.corePreimageProjection_isEssentiallySurjective

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexCompletionComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexCompletionComparison_isEssentiallySurjective := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison_isEssentiallySurjective

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison_unitIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexCompletionComparison_unitIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison_unitIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexQuotient_isEssentiallySurjective := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexQuotient_isEssentiallySurjective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexQuotient_localized_isIso_iff_completion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexQuotient_localized_isIso_iff_completion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexQuotient_localized_isIso_iff_fullyFaithful := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexQuotient_localized_isIso_iff_fullyFaithful

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexCompletionComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison._proof_1
