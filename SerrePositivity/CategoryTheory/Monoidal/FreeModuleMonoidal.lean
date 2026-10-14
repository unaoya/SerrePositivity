module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorSymmetric
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreePair
public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # 自由内部加群関手のモノイダル比較 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open MonoidalFreeModule

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- 自由加群の生成元は入力の射と両立する。 -/
@[reassoc] lemma generator_freeMap {X Y : C} (f : X ⟶ Y) :
    generator M X ≫ (freeMap M f).hom = f ≫ generator M Y := by
  change ((λ_ X).inv ≫ η[M] ▷ X) ≫ M ◁ f = f ≫ (λ_ Y).inv ≫ η[M] ▷ Y
  rw [Category.assoc, ← whisker_exchange, ← leftUnitor_inv_naturality_assoc]

/-- 単位対象から生成した自由加群を正則加群へ比較する同型。 -/
def freeUnitIso : freeObj M (𝟙_ C) ≅ Mod.regular M := by
  let h := lift M (𝟙_ C) (Mod.regular M) η[M]
  have hh : h.hom = (ρ_ M).hom := MonObj.mul_one M
  letI : ModObj M (M ⊗ (𝟙_ C)) := freeAction M (𝟙_ C)
  letI : ModObj M M := (Mod.regular M).mod
  have : IsModHom M (ρ_ M).hom := by rw [← hh]; exact h.isModHom
  have : IsModHom M (ρ_ M).inv := inferInstance
  exact {
    hom := h
    inv := Mod.Hom.mk' (ρ_ M).inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ (by
      change h.hom ≫ (ρ_ M).inv = 𝟙 _
      rw [hh, Iso.hom_inv_id])
    inv_hom_id := Mod.hom_ext _ _ (by
      change (ρ_ M).inv ≫ h.hom = 𝟙 _
      rw [hh, Iso.inv_hom_id]) }

/-- 自由加群の単位比較の順方向の基礎射は右単位同型。 -/
lemma freeUnitIso_hom : (freeUnitIso M).hom.hom = (ρ_ M).hom := MonObj.mul_one M

/-- 自由加群の単位比較の逆方向の基礎射は右単位同型の逆。 -/
lemma freeUnitIso_inv : (freeUnitIso M).inv.hom = (ρ_ M).inv := rfl

/-- 自由加群の単位比較は生成元を係数の単位へ送る。 -/
@[reassoc] lemma generator_freeUnit :
    generator M (𝟙_ C) ≫ (freeUnitIso M).hom.hom = η[M] :=
  generator_lift M (𝟙_ C) (Mod.regular M) η[M]

variable [SymmetricCategory C] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 三因子を左結合で自由加群の生成元へ分解する。 -/
@[reassoc] lemma generator_freeTriple_left (X Y Z : C) :
    generator M ((X ⊗ Y) ⊗ Z) ≫ (freePairIso M (X ⊗ Y) Z).inv.hom ≫
        (moduleMap M (freePairIso M X Y).inv (𝟙 (freeObj M Z))).hom =
      ((generator M X ⊗ₘ generator M Y) ⊗ₘ generator M Z) ≫
        tripleLeftProjection M (freeObj M X) (freeObj M Y) (freeObj M Z) := by
  rw [generator_freePair_inv_assoc]
  change (generator M (X ⊗ Y) ⊗ₘ generator M Z) ≫ projection M _ _ ≫
    map M (freePairIso M X Y).inv (𝟙 (freeObj M Z)) = _
  rw [projection_map, ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Mod.id_hom', Category.comp_id, freeObj]
  rw [generator_freePair_inv]
  simp only [tripleLeftProjection]
  rw [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
  simp only [freeObj]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 三因子を右結合で自由加群の生成元へ分解する。 -/
@[reassoc] lemma generator_freeTriple_right (X Y Z : C) :
    generator M (X ⊗ (Y ⊗ Z)) ≫ (freePairIso M X (Y ⊗ Z)).inv.hom ≫
        (moduleMap M (𝟙 (freeObj M X)) (freePairIso M Y Z).inv).hom =
      (generator M X ⊗ₘ (generator M Y ⊗ₘ generator M Z)) ≫
        tripleRightProjection M (freeObj M X) (freeObj M Y) (freeObj M Z) := by
  rw [generator_freePair_inv_assoc]
  change (generator M X ⊗ₘ generator M (Y ⊗ Z)) ≫ projection M _ _ ≫
    map M (𝟙 (freeObj M X)) (freePairIso M Y Z).inv = _
  rw [projection_map, ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Mod.id_hom', Category.comp_id, freeObj]
  rw [generator_freePair_inv]
  simp only [tripleRightProjection]
  rw [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
  simp only [freeObj]

/-- 自由加群の積の逆比較は結合子と両立する。 -/
lemma freePair_associativity_inv (X Y Z : C) :
    (freePairIso M (X ⊗ Y) Z).inv ≫
        moduleMap M (freePairIso M X Y).inv (𝟙 (freeObj M Z)) ≫
          (associatorIso M (freeObj M X) (freeObj M Y) (freeObj M Z)).hom =
      freeMap M (α_ X Y Z).hom ≫ (freePairIso M X (Y ⊗ Z)).inv ≫
        moduleMap M (𝟙 (freeObj M X)) (freePairIso M Y Z).inv := by
  apply (freeHomEquiv M ((X ⊗ Y) ⊗ Z) _).injective
  change generator M ((X ⊗ Y) ⊗ Z) ≫ (freePairIso M (X ⊗ Y) Z).inv.hom ≫
      (moduleMap M (freePairIso M X Y).inv (𝟙 (freeObj M Z))).hom ≫
        associatorHom M (freeObj M X) (freeObj M Y) (freeObj M Z) =
    generator M ((X ⊗ Y) ⊗ Z) ≫ (freeMap M (α_ X Y Z).hom).hom ≫
      (freePairIso M X (Y ⊗ Z)).inv.hom ≫
        (moduleMap M (𝟙 (freeObj M X)) (freePairIso M Y Z).inv).hom
  rw [generator_freeTriple_left_assoc, tripleLeftProjection_associatorHom,
    generator_freeMap_assoc, generator_freeTriple_right]
  rw [MonoidalCategory.associator_naturality_assoc]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 自由加群の積の逆比較は交換同型と両立する。 -/
lemma freePair_braiding_inv (X Y : C) :
    (freePairIso M X Y).inv ≫ (swapIso M (freeObj M X) (freeObj M Y)).hom =
      freeMap M (β_ X Y).hom ≫ (freePairIso M Y X).inv := by
  apply (freeHomEquiv M (X ⊗ Y) _).injective
  change generator M (X ⊗ Y) ≫ (freePairIso M X Y).inv.hom ≫
      swapHom M (freeObj M X) (freeObj M Y) =
    generator M (X ⊗ Y) ≫ (freeMap M (β_ X Y).hom).hom ≫ (freePairIso M Y X).inv.hom
  rw [generator_freePair_inv_assoc, projection_swapHom, generator_freeMap_assoc,
    generator_freePair_inv, BraidedCategory.braiding_naturality_assoc]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 自由加群の単位と積の逆比較は左単位同型と両立する。 -/
lemma freePair_leftUnit_inv (X : C) :
    (leftUnitIso M (freeObj M X)).inv =
      freeMap M (λ_ X).inv ≫ (freePairIso M (𝟙_ C) X).inv ≫
        moduleMap M (freeUnitIso M).hom (𝟙 (freeObj M X)) := by
  apply (freeHomEquiv M X _).injective
  change generator M X ≫ leftUnitInv M (freeObj M X) =
    generator M X ≫ (freeMap M (λ_ X).inv).hom ≫ (freePairIso M (𝟙_ C) X).inv.hom ≫
      map M (freeUnitIso M).hom (𝟙 (freeObj M X))
  rw [generator_freeMap_assoc, generator_freePair_inv_assoc, projection_map]
  slice_rhs 2 3 => rw [tensorHom_comp_tensorHom]
  simp only [Mod.id_hom', Category.comp_id, freeObj]
  rw [generator_freeUnit]
  rw [leftUnitInv]
  change generator M X ≫ (λ_ (M ⊗ X)).inv ≫ η[M] ▷ (M ⊗ X) ≫
      projection M (Mod.regular M) (freeObj M X) =
    (λ_ X).inv ≫ (η[M] ⊗ₘ generator M X) ≫ projection M (Mod.regular M) (freeObj M X)
  erw [leftUnitor_inv_naturality_assoc]
  simp only [tensorHom_def', Category.assoc, freeObj]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 自由加群の単位と積の逆比較は右単位同型と両立する。 -/
lemma freePair_rightUnit_inv (X : C) :
    (rightUnitIso M (freeObj M X)).inv =
      freeMap M (ρ_ X).inv ≫ (freePairIso M X (𝟙_ C)).inv ≫
        moduleMap M (𝟙 (freeObj M X)) (freeUnitIso M).hom := by
  apply (freeHomEquiv M X _).injective
  change generator M X ≫ rightUnitInv M (freeObj M X) =
    generator M X ≫ (freeMap M (ρ_ X).inv).hom ≫ (freePairIso M X (𝟙_ C)).inv.hom ≫
      map M (𝟙 (freeObj M X)) (freeUnitIso M).hom
  rw [generator_freeMap_assoc, generator_freePair_inv_assoc, projection_map]
  slice_rhs 2 3 => rw [tensorHom_comp_tensorHom]
  simp only [Mod.id_hom', Category.comp_id, freeObj]
  rw [generator_freeUnit]
  rw [rightUnitInv]
  change generator M X ≫ (ρ_ (M ⊗ X)).inv ≫ (M ⊗ X) ◁ η[M] ≫
      projection M (freeObj M X) (Mod.regular M) =
    (ρ_ X).inv ≫ (generator M X ⊗ₘ η[M]) ≫ projection M (freeObj M X) (Mod.regular M)
  erw [rightUnitor_inv_naturality_assoc]
  simp only [tensorHom_def, Category.assoc, freeObj]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 自由加群の積の逆比較は両方の入力の射に関して自然。 -/
lemma freePair_inv_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (freePairIso M X Y).inv ≫ moduleMap M (freeMap M f) (freeMap M g) =
      freeMap M (f ⊗ₘ g) ≫ (freePairIso M X' Y').inv := by
  apply (cancel_epi (freePairIso M X Y).hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← freePair_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 自由加群関手の強モノイダル構造を比較同型と逆方向の整合性から構成する。 -/
def freeMonoidalCore : (freeFunctor M).CoreMonoidal :=
  Functor.CoreMonoidal.mk' (freeUnitIso M).symm (freePairIso M)
    (μIso_inv_natural_left := by
      intro X Y f Z
      have h := freePair_inv_naturality M f (𝟙 Z)
      have hi : freeMap M (𝟙 Z) = 𝟙 (freeObj M Z) := (freeFunctor M).map_id Z
      rw [hi, tensorHom_id] at h
      exact h)
    (μIso_inv_natural_right := by
      intro X Y Z f
      have h := freePair_inv_naturality M (𝟙 Z) f
      have hi : freeMap M (𝟙 Z) = 𝟙 (freeObj M Z) := (freeFunctor M).map_id Z
      rw [hi, id_tensorHom] at h
      exact h)
    (oplax_associativity := freePair_associativity_inv M)
    (oplax_left_unitality := freePair_leftUnit_inv M)
    (oplax_right_unitality := freePair_rightUnit_inv M)

/-- 自由内部加群関手は強モノイダル関手。 -/
instance freeFunctorMonoidal : (freeFunctor M).Monoidal := (freeMonoidalCore M).toMonoidal

/-- 自由内部加群関手は交換同型も保存する強モノイダル関手。 -/
instance freeFunctorBraided : (freeFunctor M).Braided where
  toMonoidal := freeFunctorMonoidal M
  braided := by
    intro X Y
    change (freePairIso M X Y).hom ≫ freeMap M (β_ X Y).hom =
      (swapIso M (freeObj M X) (freeObj M Y)).hom ≫ (freePairIso M Y X).hom
    apply (cancel_epi (freePairIso M X Y).inv).1
    rw [Iso.inv_hom_id_assoc, ← Category.assoc, freePair_braiding_inv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.MonoidalBalancedTensor
