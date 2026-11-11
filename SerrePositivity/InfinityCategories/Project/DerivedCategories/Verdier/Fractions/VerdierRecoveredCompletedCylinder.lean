module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension

/-!
概要：保存済み実境界円柱を、元の第一行単体亜群化の K 全円柱へ延長する。
方針：始端を同じ回収済み K 実族に固定し、元の亜群化の Kan 条件を実適用する。
規約：同じ単位・実円柱・始端を保持し、境界をホモトピー類へ落とさない。
使われ方：商 core の全円柱との境界付き比較を構成する実始域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison
end SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}
  {G : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}
  {r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}

local notation "P" => S.toSSet ⊗ (Δ[1] : SSet)
local notation "J" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet) Δ[0]

namespace VerdierRecoveredInitialComparison

variable (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U)

/-- 同じ保存済み K 実全族を元の第一行単体へ移す。 -/
def simplexFamily : K ⟶ (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  corePreimageLift ((ihom (Δ[n + 1] : SSet.{u})).map q.hom)
    (r.cylinder.whole ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app B.obj) (by
      rw [Category.assoc, ← (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).naturality q.hom,
        ← Category.assoc]
      exact c.initialSource_inverts.comp
        ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj))

lemma simplexFamily_boundary : S.ι ≫ c.simplexFamily =
    (SSet.ι₀ : S.toSSet ⟶ P) ≫ (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) := by
  apply (cancel_mono (relativeFirstRowSimplex q (n + 1)).ι).mp
  change S.ι ≫ (r.cylinder.whole ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app B.obj) =
    (SSet.ι₀ : S.toSSet ⟶ P) ≫
      (r.cylinder.homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app B.obj)
  exact (congrArg (fun k => k ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app B.obj)
    r.cylinder.homotopy.h₀).symm.trans (Category.assoc _ _ _)

/-- 元の単位へ送った実 S 円柱。始端は同じ K 実全族の制限。 -/
def completedBoundaryHomotopy : SSet.Homotopy
    (S.ι ≫ (c.simplexFamily ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap
      (relativeFirstRowSimplex q (n + 1) : SSet.{u})))
    ((SSet.ι₁ : S.toSSet ⟶ P) ≫ (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap
      (relativeFirstRowSimplex q (n + 1) : SSet.{u})) where
  h := (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap _
  h₀ := by
    change (SSet.ι₀ : S.toSSet ⟶ P) ≫ (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ _ = S.ι ≫ c.simplexFamily ≫ _
    rw [← Category.assoc, ← c.simplexFamily_boundary, Category.assoc]
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro v
    exact False.elim v.1.property

end VerdierRecoveredInitialComparison

/-- 元の亜群化上の K 全円柱。元の実 S 円柱を全時刻で厳密に保持する。 -/
structure VerdierRecoveredCompletedCylinder (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) where
  endpoint : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (relativeFirstRowSimplex q (n + 1) : SSet.{u})
  homotopy : SSet.Homotopy
    (c.simplexFamily ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (relativeFirstRowSimplex q (n + 1) : SSet.{u}))
    endpoint
  boundary_eq : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (relativeFirstRowSimplex q (n + 1) : SSet.{u})
  endpoint_boundary : S.ι ≫ endpoint =
    (SSet.ι₁ : S.toSSet ⟶ P) ≫ (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap
      (relativeFirstRowSimplex q (n + 1) : SSet.{u})

/-- 実円柱の始端と境界を保った延長。有限性や新しい比較仮定は不要。 -/
lemma exists_verdierRecoveredCompletedCylinder (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder c) := by
  have hKan : SSet.modelCategoryQuillen.J.rlp
      (CategoryTheory.Limits.terminal.from
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (relativeFirstRowSimplex q (n + 1) : SSet.{u}))) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  obtain ⟨g, hg, H, hH⟩ :=
    SerrePositivity.SimplicialModel.KanMonoEndpointExtension.exists_from_zero S.ι hKan
      (c.simplexFamily ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap _) _ c.completedBoundaryHomotopy
  exact ⟨⟨g, H, hH, hg⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierRecoveredCompletedCylinder := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierRecoveredCompletedCylinder

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder._sizeOf_inst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.boundary_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.boundary_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.casesOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.endpoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.endpoint := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.endpoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.endpoint_boundary := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.endpoint_boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.homotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.homotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.homotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.mk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.rec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.recOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.completedBoundaryHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.completedBoundaryHomotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.completedBoundaryHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.simplexFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.simplexFamily := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.simplexFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.simplexFamily_boundary := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.simplexFamily_boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCompletedCylinder.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCompletedCylinder.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.completedBoundaryHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.completedBoundaryHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.completedBoundaryHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.completedBoundaryHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.completedBoundaryHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.completedBoundaryHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.simplexFamily._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.simplexFamily._proof_1
