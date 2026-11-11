module
public import SerrePositivity.KST.SConstruction.SPostcompositionFunctorIso

/-! # 完全な逆を持つ安定な入力の同値
概要：完全な単体的射の逆データと二つの coherent な逆同型を束ねる。
方針：底の quasicategory の同値を保持し、各 S_n の完全関手への持ち上げを構成する。
規約：ホモトピー圏の同値だけに弱めない。使われ方：全正有限反復実現の同値不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 完全な順逆の単体的射と coherent な二つの逆同型を持つ安定な入力の同値。 -/
structure StableModelEquivalence (X Y : StableModel.{u}) where
  /-- 完全な順方向の射。 -/
  hom : X ⟶ Y
  /-- 完全な逆方向の射。 -/
  inv : Y ⟶ X
  /-- 始域上の合成と恒等関手の coherent な同型。 -/
  homInvIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (hom.val ≫ inv.val) (𝟙 X.carrier)
  /-- 終域上の合成と恒等関手の coherent な同型。 -/
  invHomIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (inv.val ≫ hom.val) (𝟙 Y.carrier)

/-- 完全な同値は元の底の quasicategory の実際の同値を与える。 -/
def StableModelEquivalence.toQCatEquivalence {X Y : StableModel.{u}}
    (e : StableModelEquivalence X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X.carrier Y.carrier where
  hom := e.hom.val
  inv := e.inv.val
  homInvIso := e.homInvIso
  invHomIso := e.invHomIso

/-- 同じ完全な逆データで向きを反転した同値。 -/
def StableModelEquivalence.symm {X Y : StableModel.{u}}
    (e : StableModelEquivalence X Y) : StableModelEquivalence Y X where
  hom := e.inv
  inv := e.hom
  homInvIso := e.invHomIso
  invHomIso := e.homInvIso

/-- 各 S_n は完全な逆データと二つの coherent な逆同型を保つ。 -/
def StableModelEquivalence.sConstruction (n : ℕ) {X Y : StableModel.{u}}
    (e : StableModelEquivalence X Y) :
    StableModelEquivalence (sStableModel n X) (sStableModel n Y) where
  hom := (sEndofunctor n).map e.hom
  inv := (sEndofunctor n).map e.inv
  homInvIso := by
    have h := sPostcompositionFunctorIso n (f := e.hom ≫ e.inv) (g := 𝟙 X) e.homInvIso
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact h
  invHomIso := by
    have h := sPostcompositionFunctorIso n (f := e.inv ≫ e.hom) (g := 𝟙 Y) e.invHomIso
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact h

end SerrePositivity.KST.SConstruction
