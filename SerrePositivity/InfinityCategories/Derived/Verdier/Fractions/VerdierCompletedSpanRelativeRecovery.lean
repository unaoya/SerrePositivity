module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanKanComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.IntervalReplacementPathSection
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.RelativeHomotopyConstantComposition

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
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- Kan 同値の相対持ち上げは、境界を固定し比較円柱も境界上で定値にできる。 -/
lemma spanRecoveryKanEquivalence_relative {X Y S K : SSet.{u}}
    [KanComplex X] [KanComplex Y] (t : X ⟶ Y) (ht : IsQCatEquivalence t)
    (j : S ⟶ K) [Mono j] (a : S ⟶ X) (b : K ⟶ Y) (ha : a ≫ t = j ≫ b) :
    ∃ r : K ⟶ X, j ≫ r = a ∧ ∃ H : SSet.Homotopy (r ≫ t) b,
      (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst S (Δ[1] : SSet.{u}) ≫ a ≫ t := by
  have hpt : TrivialKanFibration (equivalencePathReplacementMap t) :=
    ht.choose.isFullyFaithful.equivalencePathReplacementMap.trivialKanFibration_of_surjective
      ht.choose.isEssentiallySurjective.equivalencePathReplacementMap_surjective
  have he : F2.intervalReplacementEndpoint t =
      (F2.equivalenceIntervalReplacementIso t).inv ≫ equivalencePathReplacementMap t := by
    rw [← F2.equivalenceIntervalReplacementIso_endpoint, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  have hp : TrivialKanFibration (F2.intervalReplacementEndpoint t) := by
    rw [he]
    exact ⟨trivialKanFibrations.comp_mem _ _ (MorphismProperty.of_isIso _ _)
      hpt.mem⟩
  have := TrivialKanFibration.mem (p := F2.intervalReplacementEndpoint t) j inferInstance
  have sq : CommSq (a ≫ F2.intervalReplacementSection t) j
      (F2.intervalReplacementEndpoint t) b := ⟨by
    rw [Category.assoc, F2.intervalReplacementSection_endpoint]
    exact ha⟩
  let v := sq.lift
  let pr := pullback.snd ((F2.intervalEndpointNatTrans 0).app Y) t
  let r := v ≫ pr
  have hr : j ≫ r = a := by
    dsimp only [r]
    rw [← Category.assoc, show j ≫ v = a ≫ F2.intervalReplacementSection t from sq.fac_left,
      Category.assoc, F2.intervalReplacementSection_projection, Category.comp_id]
  let P := F2.intervalReplacementCanonicalPathHomotopy t
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
    show j ≫ v = a ≫ F2.intervalReplacementSection t from sq.fac_left]
  exact F2.intervalReplacementCanonicalPathHomotopy_section_precomp t a

/-- 単位を保つ Kan 比較の任意の有限族を、指定実境界の輸送円柱とともに回収する。 -/
lemma verdierSpan_relative_finite_recovery_of_kanComparison
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {Y : SSet.{u}} [KanComplex Y]
    (b : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y ⟶ Y)
    (t : F2.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y) ⟶ Y)
    (ht : IsQCatEquivalence t)
    (hu : F2.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y) ≫ t = b)
    {K : SSet.{u}} [K.Finite] (S : K.Subcomplex) [S.toSSet.Finite]
    (a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y) (f : K ⟶ Y)
    (ha : a ≫ b = S.ι ≫ f) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d,
        ∃ L : SSet.Homotopy
          (S.ι ≫ g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d) a,
        ∃ G : SSet.Homotopy
          (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫ b) f,
          (S.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫ b := by
  let u := F2.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y)
  have hat : (a ≫ u) ≫ t = S.ι ≫ f := by
    rw [Category.assoc, hu]
    exact ha
  obtain ⟨r, hr, H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanEquivalence_relative t ht S.ι (a ≫ u) f hat
  obtain ⟨d, g, L, G, hG⟩ :=
    verdierDenominatorSpan_relative_finite_recovery h x y S.ι a r hr.symm
  let U := functorHomotopyPostcomp G t
  have hH' : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst S.toSSet (Δ[1] : SSet.{u}) ≫ S.ι ≫ (r ≫ t) := by
    rw [hH, ← Category.assoc S.ι r t, hr]
  obtain ⟨T, hT⟩ := F2.exists_relativeHomotopyComposite_right_constant S U H hH'
  let G' : SSet.Homotopy
      (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫ b) f := {
    h := T.h
    h₀ := by
      rw [T.h₀]
      change (g ≫ vertexFiberι _ _ ≫ u) ≫ t = _
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
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {K : SSet.{u}} [K.Finite] (S : K.Subcomplex) [S.toSSet.Finite]
    (a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y) = S.ι ≫ f) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d,
        ∃ L : SSet.Homotopy
          (S.ι ≫ g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d) a,
        ∃ G : SSet.Homotopy
          (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
            _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
            _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)) f,
          (S.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫
            _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
            _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y) := by
  simpa only [Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpan_relative_finite_recovery_of_kanComparison h x y
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
        _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y))
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanComparison i x y)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanComparison_isQCatEquivalence h x y)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanComparison_unit i x y) S a f ha

/-- 商の有限写像族を、指定実境界の同じ輸送経路を保って実分数族へ戻す。 -/
lemma verdierFiniteMappingFamily_relative_recovery
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {K : SSet.{u}} [K.Finite] (S : K.Subcomplex) [S.toSSet.Finite]
    (a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y)
    (f : K ⟶ intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
      (q.hom.app (Opposite.op ⦋0⦌) y))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y = S.ι ≫ f) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d,
        ∃ L : SSet.Homotopy
          (S.ι ≫ g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d) a,
        ∃ G : SSet.Homotopy
          (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
            _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
            fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y) f,
          (S.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫
            _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
            fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y := by
  simpa only [Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpan_relative_finite_recovery_of_kanComparison h x y
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
        fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanMappingComparison h x y)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanMappingComparison_isQCatEquivalence h x y)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanMappingComparison_unit h x y) S a f ha

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanEquivalence_relative := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanEquivalence_relative

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierCompletedSpan_relative_finite_recovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierCompletedSpan_relative_finite_recovery

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierFiniteMappingFamily_relative_recovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierFiniteMappingFamily_relative_recovery

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpan_relative_finite_recovery_of_kanComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpan_relative_finite_recovery_of_kanComparison
