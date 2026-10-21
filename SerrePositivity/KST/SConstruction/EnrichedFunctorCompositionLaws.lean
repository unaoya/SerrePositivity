module
public import Mathlib.CategoryTheory.Enriched.Basic

/-! # 実豊穣関手の合成の厳密な法則
概要：元の対象作用と全 Hom 作用を持つ豊穣関手の合成の結合・単位を回収する。
方針：豊穣関手の同値判定と、元の Hom 圏での合成の法則を使う。
規約：対象と Hom の移送を変えない。使われ方：Λ の oplax tensor の合成比較。
-/
@[expose] public section
universe v u w₁ w₂ w₃ w₄
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  {B : Type w₁} {C : Type w₂} {D : Type w₃} {E : Type w₄}
  [EnrichedCategory V B] [EnrichedCategory V C] [EnrichedCategory V D] [EnrichedCategory V E]

/-- 元の三つの実豊穣関手の合成は厳密に結合的。 -/
lemma enrichedFunctor_comp_assoc (F : EnrichedFunctor V B C) (G : EnrichedFunctor V C D)
    (H : EnrichedFunctor V D E) :
    EnrichedFunctor.comp V (EnrichedFunctor.comp V F G) H =
      EnrichedFunctor.comp V F (EnrichedFunctor.comp V G H) := by
  refine EnrichedFunctor.ext V
    (F := EnrichedFunctor.comp V (EnrichedFunctor.comp V F G) H)
    (G := EnrichedFunctor.comp V F (EnrichedFunctor.comp V G H)) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (Category.assoc _ _ _)

/-- 元の実豊穣関手の左の恒等合成は同じ関手。 -/
lemma enrichedFunctor_id_comp (F : EnrichedFunctor V B C) :
    EnrichedFunctor.comp V (EnrichedFunctor.id V B) F = F := by
  refine EnrichedFunctor.ext V (F := EnrichedFunctor.comp V (EnrichedFunctor.id V B) F)
    (G := F) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (Category.id_comp _)

/-- 元の実豊穣関手の右の恒等合成は同じ関手。 -/
lemma enrichedFunctor_comp_id (F : EnrichedFunctor V B C) :
    EnrichedFunctor.comp V F (EnrichedFunctor.id V C) = F := by
  refine EnrichedFunctor.ext V (F := EnrichedFunctor.comp V F (EnrichedFunctor.id V C))
    (G := F) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (Category.comp_id _)

end SerrePositivity.KST.SConstruction
