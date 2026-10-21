module

public import SerrePositivity.KST.Comparison.ExInfinityMonoidal
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# 同じ Ex∞ による実豊穣関手の移送

概要：元の Hom 射へ同じ Ex∞ を作用させ、単位と合成を保つ。
方針：同じ monoidal 構造の自然性と元の豊穣関手の二つの正方形を使う。
規約：元の対象写像と元の Hom 射の像を保持する。
使われ方：自由 hammock の両比較の Kan 化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory SerrePositivity.KST.Comparison
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  {D : Type w} [EnrichedCategory SSet.{u} D]

def exInfinityEnrichedFunctor (F : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctor SSet.{u} (TransportEnrichment exInfinity C)
      (TransportEnrichment exInfinity D) where
  obj X := F.obj X
  map X Y := exInfinity.map (F.map X Y)
  map_id X := by
    change (Functor.LaxMonoidal.ε exInfinity ≫ exInfinity.map (eId (C := C) SSet.{u} X)) ≫
      exInfinity.map (F.map X X) =
        Functor.LaxMonoidal.ε exInfinity ≫ exInfinity.map (eId (C := D) SSet.{u} (F.obj X))
    rw [Category.assoc, ← exInfinity.map_comp, F.map_id]
  map_comp X Y Z := by
    change (Functor.LaxMonoidal.μ exInfinity _ _ ≫ exInfinity.map (eComp (C := C) SSet.{u} X Y Z)) ≫
      exInfinity.map (F.map X Z) =
        (exInfinity.map (F.map X Y) ⊗ₘ exInfinity.map (F.map Y Z)) ≫
          Functor.LaxMonoidal.μ exInfinity _ _ ≫
            exInfinity.map (eComp (C := D) SSet.{u} (F.obj X) (F.obj Y) (F.obj Z))
    rw [Category.assoc, ← exInfinity.map_comp, F.map_comp, exInfinity.map_comp,
      ← Category.assoc, ← Functor.LaxMonoidal.μ_natural, Category.assoc]

lemma exInfinityEnrichedFunctor_map (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    (exInfinityEnrichedFunctor F).map X Y = exInfinity.map (F.map X Y) := rfl

instance exInfinityTransportHom_kanComplex (X Y : TransportEnrichment exInfinity.{u} C) :
    SSet.KanComplex (X ⟶[SSet.{u}] Y) := by
  change SSet.KanComplex (exInfinity.obj ((show C from X) ⟶[SSet.{u}] (show C from Y)))
  infer_instance

end SerrePositivity.EInfinity.Hammock
