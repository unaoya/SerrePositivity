module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteFactorization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiniteMappingCylinder
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の亜群化の有限全族・指定境界族・指定境界 Homotopy を同じ有限台へ下ろす。
方針：元の境界円柱を有限写像円柱上の一射へ貼り、一つの全因子化同型を制限する。
規約：有限台と全比較は一つを共有し、境界比較を点ごとに選び直さない。
使われ方：c5 の任意の完成側有限境界と比較円柱の同時処理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary
end SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {L K X : SSet.{u}} (j : L ⟶ K) (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion X)
  {a : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion X} (H : SSet.Homotopy a (j ≫ f))

/-- 指定された元の境界 Homotopy と全族を貼った一つの全写像。 -/
def completedBoundaryCylinderMap : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion X :=
  pushout.desc ((β_ (Δ[1] : SSet.{u}) L).hom ≫ H.h) f (by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
    exact H.h₁)

lemma completedBoundaryCylinderMap_family :
    pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 L) j ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H = f :=
  pushout.inr_desc _ _ _

lemma completedBoundaryCylinderMap_boundary :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H = a := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap,
    pushout.inl_desc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
  exact H.h₀

lemma completedBoundaryCylinderMap_prism :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H = H.h := by
  change ((β_ L (Δ[1] : SSet.{u})).hom ≫ pushout.inl _ _) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap, pushout.inl_desc,
    ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 有限な元の境界円柱全体を、一つの元の有限部分複体の完成へ移したデータ。 -/
structure GroupoidCompletionFiniteBoundary where
  support : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex X
  whole : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion support.val
  comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (whole ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf support.val.ι)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H)

/-- 任意の有限境界・全族・境界比較を、同じ一つの有限台と全同型で同時に回収する。 -/
lemma exists_groupoidCompletionFiniteBoundary [L.Finite] [K.Finite] :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary j f H) := by
  obtain ⟨A, b, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletion_finite_factorization
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H)
  exact ⟨⟨A, b, e⟩⟩

namespace GroupoidCompletionFiniteBoundary

variable {j f H} (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary j f H)

def family : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion d.support.val :=
  pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 L) j ≫ d.whole

def boundary : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion d.support.val :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j ≫ d.whole

/-- 同じ有限台上の、指定境界から全族の制限への実 Homotopy。 -/
def boundaryHomotopy : SSet.Homotopy d.boundary (j ≫ d.family) := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j) d.whole
  exact { h := V.h, h₀ := V.h₀, h₁ := V.h₁.trans (Category.assoc _ _ _), rel := V.rel }

/-- 同じ一つの全比較の K 制限。 -/
def familyIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.family ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf d.support.val.ι) f := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp d.comparison (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 L) j)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.family, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap_family] using e

/-- 同じ一つの全比較の L 始端制限。 -/
def boundaryIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.boundary ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf d.support.val.ι) a := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp d.comparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundary, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap_boundary] using e

/-- 同じ一つの全比較の全境界円柱制限。 -/
def boundaryPrismIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (d.boundaryHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf d.support.val.ι) H.h := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp d.comparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap_prism] using e

end GroupoidCompletionFiniteBoundary
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.completedBoundaryCylinderMap := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.completedBoundaryCylinderMap_boundary := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.completedBoundaryCylinderMap_family := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap_family

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.completedBoundaryCylinderMap_prism := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap_prism

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_groupoidCompletionFiniteBoundary := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.exists_groupoidCompletionFiniteBoundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundary (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundary := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryHomotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryPrismIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryPrismIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryPrismIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.casesOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.comparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.comparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.family (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.family := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.family

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.familyIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.familyIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.familyIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.mk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.rec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.recOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.support (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.support := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.support

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.whole (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.whole := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.whole

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.completedBoundaryCylinderMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.completedBoundaryCylinderMap.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundary.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundary.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryHomotopy.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryHomotopy.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryPrismIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryPrismIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.boundaryPrismIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.boundaryPrismIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.family._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.family._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.family._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.family._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.family.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.family.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.familyIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.familyIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.familyIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.familyIso._proof_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary.mk.sizeOf_spec
