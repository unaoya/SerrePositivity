module
public import SerrePositivity.KST.SConstruction.NecklaceCubicalUnitLaws
public import SerrePositivity.KST.SConstruction.NecklaceCubicalAssociativity
public import SerrePositivity.KST.SConstruction.NecklaceCubicalCompositionNaturality
public import Mathlib.CategoryTheory.Enriched.Basic

/-! # 元の全 necklace による cubical rigidification
概要：単体集合の零単体を対象とし、全 necklace の mapping object で豊穣圏を作る。
方針：元の一点・wedge の合成と、全余極限上の左右単位・結合則を束ねる。
規約：Rivera–Zeinalian Definition 3.3 の元の図式を使う。使われ方：Λ と dg nerve。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet

/-- 元の零単体を対象に持つ cubical rigidification の対象型。 -/
def CubicalRigidification (K : SSet.{u}) : Type u := K _⦋0⦌

/-- Rigidification の対象は元の零単体と同じ。 -/
def cubicalRigidificationVertexEquiv (K : SSet.{u}) : CubicalRigidification K ≃ K _⦋0⦌ :=
  Equiv.refl _

/-- 元の全 necklace の余極限による、Day cubical sets 上の実豊穣圏。 -/
instance cubicalRigidificationEnriched (K : SSet.{u}) :
    EnrichedCategory CubicalDaySet.{u} (CubicalRigidification K) where
  Hom x y := necklaceCubicalDayMapping K x y
  id x := necklaceCubicalDayIdentity K x
  comp x y z := necklaceCubicalDayCompose K x y z
  id_comp x y :=
    (congrArg (fun b => (λ_ (necklaceCubicalDayMapping K x y)).inv ≫ b)
      (necklaceCubicalDay_left_unit K x y)).trans (Iso.inv_hom_id _)
  comp_id x y :=
    (congrArg (fun b => (ρ_ (necklaceCubicalDayMapping K x y)).inv ≫ b)
      (necklaceCubicalDay_right_unit K x y)).trans (Iso.inv_hom_id _)
  assoc w x y z :=
    (congrArg (fun b =>
      (α_ (necklaceCubicalDayMapping K w x) (necklaceCubicalDayMapping K x y)
        (necklaceCubicalDayMapping K y z)).inv ≫ b)
      (necklaceCubicalDay_assoc K w x y z)).trans (Iso.inv_hom_id_assoc _ _)

/-- 豊穣 Hom は元の全 necklace の cubical mapping object そのもの。 -/
lemma cubicalRigidification_hom (K : SSet.{u}) (x y : CubicalRigidification K) :
    (x ⟶[CubicalDaySet.{u}] y).functor = necklaceCubicalMapping K x y := rfl

/-- 豊穣単位は元の一点 necklace による単位射そのもの。 -/
lemma cubicalRigidification_id (K : SSet.{u}) (x : CubicalRigidification K) :
    (eId CubicalDaySet.{u} x).natTrans = necklaceCubicalIdentity K x := rfl

/-- 豊穣合成は元の mapping object 全体へ降ろした合成そのもの。 -/
lemma cubicalRigidification_comp (K : SSet.{u}) (x y z : CubicalRigidification K) :
    (eComp CubicalDaySet.{u} x y z).natTrans = necklaceCubicalCompose K x y z := rfl

/-- 元の単体的写像は、全 necklace の後合成による実豊穣関手を定める。 -/
def cubicalRigidificationMap {K L : SSet.{u}} (a : K ⟶ L) :
    EnrichedFunctor CubicalDaySet.{u} (CubicalRigidification K) (CubicalRigidification L) where
  obj x := a.app _ x
  map x y := .mk (necklaceCubicalMap a x y)
  map_id x := DayFunctor.hom_ext (necklaceCubicalIdentity_naturality a x)
  map_comp x y z := DayFunctor.hom_ext (necklaceCubicalCompose_naturality a x y z)

/-- 元の入力写像の対象作用は、元の零単体への作用そのもの。 -/
lemma cubicalRigidificationMap_obj {K L : SSet.{u}} (a : K ⟶ L)
    (x : CubicalRigidification K) : (cubicalRigidificationMap a).obj x = a.app _ x := rfl

/-- 元の入力写像の Hom 作用は、元の全 necklace の余極限上の射そのもの。 -/
lemma cubicalRigidificationMap_map {K L : SSet.{u}} (a : K ⟶ L)
    (x y : CubicalRigidification K) :
    ((cubicalRigidificationMap a).map x y).natTrans = necklaceCubicalMap a x y := rfl

/-- 元の恒等入力は、実豊穣関手の恒等を厳密に回収する。 -/
lemma cubicalRigidificationMap_id (K : SSet.{u}) :
    cubicalRigidificationMap (𝟙 K) =
      EnrichedFunctor.id CubicalDaySet.{u} (CubicalRigidification K) := by
  refine EnrichedFunctor.ext CubicalDaySet.{u}
    (F := cubicalRigidificationMap (𝟙 K))
    (G := EnrichedFunctor.id CubicalDaySet.{u} (CubicalRigidification K))
    (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (DayFunctor.hom_ext (necklaceCubicalMap_id K x y))

/-- 元の入力の合成は、実豊穣関手の合成と厳密に一致する。 -/
lemma cubicalRigidificationMap_comp {K L M : SSet.{u}} (a : K ⟶ L) (b : L ⟶ M) :
    cubicalRigidificationMap (a ≫ b) =
      EnrichedFunctor.comp CubicalDaySet.{u}
        (cubicalRigidificationMap a) (cubicalRigidificationMap b) := by
  refine EnrichedFunctor.ext CubicalDaySet.{u}
    (F := cubicalRigidificationMap (a ≫ b))
    (G := EnrichedFunctor.comp CubicalDaySet.{u}
      (cubicalRigidificationMap a) (cubicalRigidificationMap b)) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans
    (DayFunctor.hom_ext (necklaceCubicalMap_comp a b x y))

end SerrePositivity.KST.SConstruction
