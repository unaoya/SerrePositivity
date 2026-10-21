module
public import Mathlib.CategoryTheory.Enriched.Basic

/-! # モノイダル関手による実豊穣関手の移送
概要：既存の豊穣圏の移送に、元の実豊穣関手の Hom 作用を接続する。
方針：単位と合成保存を、同じ lax monoidal 関手の自然性で移す。
規約：対象作用と全 Hom 作用を保持。使われ方：cubical rigidification の Serre 鎖。
-/
@[expose] public section
noncomputable section
universe v v' u u' w w'
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  {W : Type u'} [Category.{v'} W] [MonoidalCategory W]
  (F : V ⥤ W) [F.LaxMonoidal]
  {C : Type w} {D : Type w'} [EnrichedCategory V C] [EnrichedCategory V D]

/-- 元の豊穣関手を、同じモノイダル関手による豊穣圏の移送へ送る。 -/
def enrichedFunctorTransport (E : EnrichedFunctor V C D) :
    EnrichedFunctor W (TransportEnrichment F C) (TransportEnrichment F D) where
  obj := E.obj
  map x y := F.map (E.map x y)
  map_id x := by
    change C at x
    change (Functor.LaxMonoidal.ε F ≫ F.map (eId (C := C) V x)) ≫ F.map (E.map x x) =
      Functor.LaxMonoidal.ε F ≫ F.map (eId (C := D) V (E.obj x))
    rw [Category.assoc, ← F.map_comp, E.map_id]
  map_comp x y z := by
    change C at x y z
    change (Functor.LaxMonoidal.μ F _ _ ≫ F.map (eComp (C := C) V x y z)) ≫
        F.map (E.map x z) =
      (F.map (E.map x y) ⊗ₘ F.map (E.map y z)) ≫
        Functor.LaxMonoidal.μ F _ _ ≫ F.map (eComp (C := D) V (E.obj x) (E.obj y) (E.obj z))
    rw [Category.assoc, ← F.map_comp, E.map_comp, F.map_comp]
    rw [← Functor.LaxMonoidal.μ_natural_assoc]

/-- 移送は元の対象作用を保持する。 -/
lemma enrichedFunctorTransport_obj (E : EnrichedFunctor V C D) (x : TransportEnrichment F C) :
    (enrichedFunctorTransport F E).obj x = E.obj x := rfl

/-- 移送の Hom 作用は、元の Hom 作用の同じ関手による像。 -/
lemma enrichedFunctorTransport_map (E : EnrichedFunctor V C D)
    (x y : TransportEnrichment F C) :
    (enrichedFunctorTransport F E).map x y = F.map (E.map x y) := rfl

/-- 移送は実豊穣関手の恒等を厳密に保つ。 -/
lemma enrichedFunctorTransport_id :
    enrichedFunctorTransport F (EnrichedFunctor.id V C) =
      EnrichedFunctor.id W (TransportEnrichment F C) := by
  refine EnrichedFunctor.ext W
    (F := enrichedFunctorTransport F (EnrichedFunctor.id V C))
    (G := EnrichedFunctor.id W (TransportEnrichment F C)) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (F.map_id _)

/-- 移送は実豊穣関手の合成を厳密に保つ。 -/
lemma enrichedFunctorTransport_comp {B : Type*} [EnrichedCategory V B]
    (E : EnrichedFunctor V C D) (G : EnrichedFunctor V D B) :
    enrichedFunctorTransport F (EnrichedFunctor.comp V E G) =
      EnrichedFunctor.comp W (enrichedFunctorTransport F E) (enrichedFunctorTransport F G) := by
  refine EnrichedFunctor.ext W
    (F := enrichedFunctorTransport F (EnrichedFunctor.comp V E G))
    (G := EnrichedFunctor.comp W (enrichedFunctorTransport F E)
      (enrichedFunctorTransport F G)) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (F.map_comp _ _)

end SerrePositivity.KST.SConstruction
