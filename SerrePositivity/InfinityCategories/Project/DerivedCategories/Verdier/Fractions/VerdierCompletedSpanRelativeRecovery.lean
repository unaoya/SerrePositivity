module


public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSpanKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementPathSection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeHomotopyConstantComposition

/-!
概要：元の完成分数の有限族を、指定実境界の輸送円柱を保って実分母族へ戻す。
方針：単位を保つ Kan 比較の相対持ち上げと、実分母への相対回収を合成する。
規約：境界の比較経路は元の実輸送円柱の像に厳密に一致する。
使われ方：第一行単体比較の共有経路を新仮定なしで構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- Kan 同値の相対持ち上げは、境界を固定し比較円柱も境界上で定値にできる。 -/
lemma spanRecoveryKanEquivalence_relative {X Y S K : SSet.{u}}
    [KanComplex X] [KanComplex Y] (t : X ⟶ Y) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence t)
    (j : S ⟶ K) [Mono j] (a : S ⟶ X) (b : K ⟶ Y) (ha : a ≫ t = j ≫ b) :
    ∃ r : K ⟶ X, j ≫ r = a ∧ ∃ H : SSet.Homotopy (r ≫ t) b,
      (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst S (Δ[1] : SSet.{u}) ≫ a ≫ t := by
  have hpt : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap t) :=
    ht.choose.isFullyFaithful.equivalencePathReplacementMap.trivialKanFibration_of_surjective
      ht.choose.isEssentiallySurjective.equivalencePathReplacementMap_surjective
  have he : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint t =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso t).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap t := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso_endpoint, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint t) := by
    rw [he]
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ (MorphismProperty.of_isIso _ _)
      hpt.mem⟩
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint t) j inferInstance
  have sq : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection t) j
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint t) b := ⟨by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection_endpoint]
    exact ha⟩
  let v := sq.lift
  let pr := pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) t
  let r := v ≫ pr
  have hr : j ≫ r = a := by
    dsimp only [r]
    rw [← Category.assoc, show j ≫ v = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection t from sq.fac_left,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection_projection, Category.comp_id]
  let P := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementCanonicalPathHomotopy t
  let H : SSet.Homotopy (r ≫ t) b := {
    h := (v ▷ (Δ[1] : SSet.{u})) ≫ P.h
    h₀ := by
      rw [SSet.ι₀_comp_assoc, P.h₀]
      exact (Category.assoc _ _ _).symm
    h₁ := by
      rw [SSet.ι₁_comp_assoc, P.h₁]
      exact sq.fac_right
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  refine ⟨r, hr, H, ?_⟩
  change (j ▷ (Δ[1] : SSet.{u})) ≫ (v ▷ (Δ[1] : SSet.{u})) ≫ P.h = _
  rw [← comp_whiskerRight_assoc,
    show j ≫ v = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection t from sq.fac_left]
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementCanonicalPathHomotopy_section_precomp t a

/-- 単位を保つ Kan 比較の任意の有限族を、指定実境界の輸送円柱とともに回収する。 -/
lemma verdierSpan_relative_finite_recovery_of_kanComparison
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {Y : SSet.{u}} [KanComplex Y]
    (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y ⟶ Y)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y) ⟶ Y)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence t)
    (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y) ≫ t = b)
    {K : SSet.{u}} [K.Finite] (S : K.Subcomplex) [S.toSSet.Finite]
    (a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y) (f : K ⟶ Y)
    (ha : a ≫ b = S.ι ≫ f) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d,
        ∃ L : SSet.Homotopy
          (S.ι ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d) a,
        ∃ G : SSet.Homotopy
          (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫ b) f,
          (S.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫ b := by
  let u := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y)
  have hat : (a ≫ u) ≫ t = S.ι ≫ f := by
    rw [Category.assoc, hu]
    exact ha
  obtain ⟨r, hr, H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanRecoveryKanEquivalence_relative t ht S.ι (a ≫ u) f hat
  obtain ⟨d, g, L, G, hG⟩ :=
    verdierDenominatorSpan_relative_finite_recovery h x y S.ι a r hr.symm
  let U := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp G t
  have hH' : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst S.toSSet (Δ[1] : SSet.{u}) ≫ S.ι ≫ (r ≫ t) := by
    rw [hH, ← Category.assoc S.ι r t, hr]
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyComposite_right_constant S U H hH'
  let G' : SSet.Homotopy
      (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫ b) f := {
    h := T.h
    h₀ := by
      rw [T.h₀]
      change (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ u) ≫ t = _
      rw [Category.assoc, Category.assoc, hu]
      rfl
    h₁ := T.h₁
    rel := T.rel }
  refine ⟨d, g, L, G', ?_⟩
  change (S.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h = _
  rw [hT]
  change (S.ι ▷ (Δ[1] : SSet.{u})) ≫ (G.h ≫ t) = _
  rw [← Category.assoc, hG, Category.assoc, hu]

/-- 完成分数の有限族は、指定実境界の同じ全輸送円柱を保って回収できる。 -/
lemma verdierCompletedSpan_relative_finite_recovery
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {K : SSet.{u}} [K.Finite] (S : K.Subcomplex) [S.toSSet.Finite]
    (a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) = S.ι ≫ f) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d,
        ∃ L : SSet.Homotopy
          (S.ι ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d) a,
        ∃ G : SSet.Homotopy
          (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)) f,
          (S.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) := by
  simpa only [Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpan_relative_finite_recovery_of_kanComparison h x y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanKanComparison i x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanKanComparison_isQCatEquivalence h x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanKanComparison_unit i x y) S a f ha

/-- 商の有限写像族を、指定実境界の同じ輸送経路を保って実分数族へ戻す。 -/
lemma verdierFiniteMappingFamily_relative_recovery
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {K : SSet.{u}} [K.Finite] (S : K.Subcomplex) [S.toSSet.Finite]
    (a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
      (q.hom.app (Opposite.op ⦋0⦌) y))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y = S.ι ≫ f) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d,
        ∃ L : SSet.Homotopy
          (S.ι ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d) a,
        ∃ G : SSet.Homotopy
          (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
            fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y) f,
          (S.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
            fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y := by
  simpa only [Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpan_relative_finite_recovery_of_kanComparison h x y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
        fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanKanMappingComparison h x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanKanMappingComparison_isQCatEquivalence h x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanKanMappingComparison_unit h x y) S a f ha

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
