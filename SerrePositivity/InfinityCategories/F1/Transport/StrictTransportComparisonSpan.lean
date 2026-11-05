module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftCoherentTransportReconstruction

/-! # strict transport の元の二脚と weighted 比較への因子分解を保持する復元 span -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.Fibration.StrictTransportComparisonSpan
end SerrePositivity.KST.Fibration.StrictTransportComparisonSpan
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- 元の strict transport の共通全空間と二脚を、底の条件とともに保持する。 -/
structure StrictTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] where
  total : SSet.{u}
  projection : _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.total ⟶ nerve I
  source : _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.total ⟶ E
  weighted : _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.total ⟶ leftStrictTransportWeightedNerve p
  inner : InnerFibration _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.projection
  source_over : _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.source ≫ p = _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.projection
  weighted_over : _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.weighted ≫ leftStrictTransportWeightedProjection p = _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.projection
  source_equivalence : IsPrecompositionEquivalence _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.source
  weighted_equivalence : IsPrecompositionEquivalence _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.weighted

/-- 構成済みの strict 復元 span を、元の二脚を保持するデータとして受け取る。 -/
theorem nonempty_strictTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] : Nonempty (_root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan p) := by
  obtain ⟨Z, t, a, b, ht, ha, hb, ea, eb⟩ := exists_leftStrictTransport_reconstruction_span p
  exact ⟨⟨Z, t, a, b, ht, ha, hb, ea, eb⟩⟩

/-- 選択する対象に元の全空間・二脚・底上の条件をすべて含める。 -/
def strictTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] : _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan p :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.F1.Transport.nonempty_strictTransportComparisonSpan p)

namespace StrictTransportComparisonSpan
open _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan p)

/-- coherent な復元の元の共通底。 -/
def coherentBase : (SSet.uliftFunctor.{u + 1, u}).obj s.total ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) :=
  (SSet.uliftFunctor.{u + 1, u}).map s.projection

/-- coherent な復元でも、元の source 脚をそのまま持ち上げる。 -/
def coherentSource : (SSet.uliftFunctor.{u + 1, u}).obj s.total ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj E :=
  (SSet.uliftFunctor.{u + 1, u}).map s.source

/-- 元の weighted 脚と同じ既存比較を合成した、因子分解を保持する target 脚。 -/
def coherentTarget : (SSet.uliftFunctor.{u + 1, u}).obj s.total ⟶
    leftUnstraightening (leftCoherentTransport p) :=
  (SSet.uliftFunctor.{u + 1, u}).map s.weighted ≫ leftCoherentTransportComparison p

/-- 持ち上げた同じ source 脚は、元の共通底を厳密に保つ。 -/
theorem coherentSource_over :
    s.coherentSource ≫ (SSet.uliftFunctor.{u + 1, u}).map p = s.coherentBase := by
  rw [_root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentSource, _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentBase, ← Functor.map_comp, s.source_over]

/-- 同じ weighted 比較を通る target 脚も、元の共通底を厳密に保つ。 -/
theorem coherentTarget_over :
    s.coherentTarget ≫ leftUnstraighteningProjection (leftCoherentTransport p) =
      s.coherentBase := by
  rw [_root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentTarget, Category.assoc, leftCoherentTransportComparison_projection,
    ← Functor.map_comp, s.weighted_over]
  rfl

/-- 元の source 脚の同値性は、同じ宇宙持ち上げで保たれる。 -/
theorem coherentSource_equivalence : IsPrecompositionEquivalence s.coherentSource := by
  have : InnerFibration s.projection := s.inner
  have : Quasicategory s.total := quasicategory_of_innerFibration s.projection
  have : Quasicategory E := quasicategory_of_innerFibration p
  exact s.source_equivalence.isQCatEquivalence.ulift.isPrecompositionEquivalence

/-- 元の weighted 脚と同じ比較の合成も前合成同値。 -/
theorem coherentTarget_equivalence : IsPrecompositionEquivalence s.coherentTarget := by
  have : InnerFibration s.projection := s.inner
  have : Quasicategory s.total := quasicategory_of_innerFibration s.projection
  have : Quasicategory (leftStrictTransportWeightedNerve p) :=
    quasicategory_of_innerFibration (leftStrictTransportWeightedProjection p)
  exact s.weighted_equivalence.isQCatEquivalence.ulift.isPrecompositionEquivalence.comp
    (leftCoherentTransportComparison_isPrecompositionEquivalence p)

end StrictTransportComparisonSpan
end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.nonempty_strictTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.F1.Transport.nonempty_strictTransportComparisonSpan

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.strictTransportComparisonSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.F1.Transport.strictTransportComparisonSpan

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.casesOn := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentBase (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentBase := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentBase

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentSource (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentSource := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentSource

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentSource_equivalence := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentSource_equivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentSource_over := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentSource_over

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentTarget (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentTarget := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentTarget

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentTarget_equivalence := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentTarget_equivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentTarget_over := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentTarget_over

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.ctorIdx := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.inner := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.inner

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.mk := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.noConfusion := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.noConfusionType := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.projection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.projection := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.projection

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.rec := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.recOn := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.source (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.source := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.source_equivalence := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.source_equivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.source_over := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.source_over

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.total (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.total := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.total

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.weighted (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.weighted := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.weighted

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.weighted_equivalence := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.weighted_equivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.weighted_over := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.weighted_over

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentBase.eq_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentBase.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentSource.eq_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentSource.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentTarget.eq_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentTarget.eq_1

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.mk.inj := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.mk.injEq := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.mk.sizeOf_spec
