module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：底の同値は、実際の制限関手により空間値前層の ∞ 圏の同値を与える。
方針：逆射と関手同型を反転し、宇宙持ち上げと内部 Hom の前合成を順に使う。
規約：同値の順方向は元の射に沿う制限に固定する。
使われ方：F1-2 の前層 ∞ 圏を底の同値に沿って移す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- quasicategory の同値の両射を反転すると、反対 ∞ 圏の間の同値となる。 -/
def oppositeQCatEquivalence {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C D) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C.op D.op where
  hom := SSet.opFunctor.map e.hom
  inv := SSet.opFunctor.map e.inv
  homInvIso := by
    have h := e.homInvIso.op
    rw [SSet.opFunctor.map_comp, SSet.opFunctor.map_id C] at h
    exact h
  invHomIso := by
    have h := e.invHomIso.op
    rw [SSet.opFunctor.map_comp, SSet.opFunctor.map_id D] at h
    exact h

/-- 指定された同値の射は、反転後も同じ逆データで同値。 -/
lemma IsQCatEquivalence.opposite {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {f : C ⟶ D} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (SSet.opFunctor.map f) :=
  (oppositeQCatEquivalence hf.choose).isQCatEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsQCatEquivalence (opposite)


/-- 底の同値に沿う元の前層制限関手は、quasicategory の同値。 -/
lemma presheafInfinityRestriction_isQCatEquivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] {f : C ⟶ D} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityRestriction f) :=
  hf.opposite.ulift.precompose _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}

/-- 底の同値による前層圏の同値。順方向は指定した底の射への制限。 -/
def presheafInfinityRestrictionEquivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] {f : C ⟶ D} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity D) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) :=
  (presheafInfinityRestriction_isQCatEquivalence hf).choose

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
