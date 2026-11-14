module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedMappingLaws
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-! # 余錐成分への全豊穣族の自然性と単位
概要：余錐への後合成が、元の図式射への制限と整合することを示す。
方針：前後合成の交換と元の豊穣自然性・単位律を使う。
規約：全 Hom の等号。使われ方：実押し出しへの厳密豊穣関手。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory

/-- 元の図式射に自然な全族は、余錐成分で写した後にも同じ自然性を持つ。 -/
lemma enriched_cocone_family (V : Type u) [Category.{v} V] [MonoidalCategory V]
    {D : Type w} [Category.{z} D] [EnrichedOrdinaryCategory V D]
    {X₀ X₁ Y₀ Y₁ Q : D} (s : X₀ ⟶ X₁) (t : Y₀ ⟶ Y₁) (j : Y₁ ⟶ Q)
    {P : V} (a₀ : P ⟶ (X₀ ⟶[V] Y₀)) (a₁ : P ⟶ (X₁ ⟶[V] Y₁))
    (h : a₀ ≫ eHomWhiskerLeft V X₀ t = a₁ ≫ eHomWhiskerRight V s Y₁) :
    (a₁ ≫ eHomWhiskerLeft V X₁ j) ≫ eHomWhiskerRight V s Q =
      a₀ ≫ eHomWhiskerLeft V X₀ (t ≫ j) := by
  rw [Category.assoc, eHom_whisker_exchange, ← Category.assoc, ← h,
    Category.assoc, ← eHomWhiskerLeft_comp]

/-- 元の余錐成分の両側の豊穣恒等射は、前後合成で同じ全族を与える。 -/
lemma simplicialIdentity_whisker {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {X Y : D} (j : X ⟶ Y) :
    eId SSet.{u} X ≫ eHomWhiskerLeft SSet X j =
      eId SSet.{u} Y ≫ eHomWhiskerRight SSet j Y := by
  ext n p
  change PUnit.{u + 1} at p
  have hp : p = PUnit.unit := Subsingleton.elim _ _
  subst p
  change (eComp SSet X X Y).app n
      ((eId SSet X).app n PUnit.unit, (eHomEquiv SSet j).app n PUnit.unit) =
    (eComp SSet X Y Y).app n
      ((eHomEquiv SSet j).app n PUnit.unit, (eId SSet Y).app n PUnit.unit)
  have hl := types_congr_hom (NatTrans.congr_app (e_id_comp SSet X Y) n)
    ((eHomEquiv SSet j).app n PUnit.unit)
  have hr := types_congr_hom (NatTrans.congr_app (e_comp_id SSet X Y) n)
    ((eHomEquiv SSet j).app n PUnit.unit)
  exact hl.trans hr.symm

end SerrePositivity.KST.SConstruction
