module

public import SerrePositivity.InfinityCategories.F1.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.F1.UniverseQCatEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence

/-!
概要：底の同値は、実際の制限関手により空間値前層の ∞ 圏の同値を与える。
方針：逆射と関手同型を反転し、宇宙持ち上げと内部 Hom の前合成を順に使う。
規約：同値の順方向は元の射に沿う制限に固定する。
使われ方：F1-2 の前層 ∞ 圏を底の同値に沿って移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- quasicategory の同値の両射を反転すると、反対 ∞ 圏の間の同値となる。 -/
def oppositeQCatEquivalence {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (e : QCatEquivalence C D) : QCatEquivalence C.op D.op where
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
    {f : C ⟶ D} (hf : IsQCatEquivalence f) : IsQCatEquivalence (SSet.opFunctor.map f) :=
  (oppositeQCatEquivalence hf.choose).isQCatEquivalence

/-- 底の同値に沿う元の前層制限関手は、quasicategory の同値。 -/
lemma presheafInfinityRestriction_isQCatEquivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] {f : C ⟶ D} (hf : IsQCatEquivalence f) :
    IsQCatEquivalence (presheafInfinityRestriction f) :=
  hf.opposite.ulift.precompose SpaceInfinity.{u}

/-- 底の同値による前層圏の同値。順方向は指定した底の射への制限。 -/
def presheafInfinityRestrictionEquivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] {f : C ⟶ D} (hf : IsQCatEquivalence f) :
    QCatEquivalence (PresheafInfinity D) (PresheafInfinity C) :=
  (presheafInfinityRestriction_isQCatEquivalence hf).choose

end SerrePositivity.InfinityCategories
