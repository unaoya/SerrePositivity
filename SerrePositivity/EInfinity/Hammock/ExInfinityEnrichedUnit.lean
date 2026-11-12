module

public import SerrePositivity.EInfinity.Hammock.ExInfinityEnrichedFunctor

/-!
# 同じ Ex∞ 単位の実豊穣関手

概要：元の全豊穣 Hom の Ex∞ 単位を一つの豊穣関手へ束ねる。
方針：元の単位の自然性・monoidal な単位則・tensor 則を使う。
規約：元の対象・単位・合成・各 Hom の同じ Ex∞ 単位を保持する。
使われ方：通常圏から Kan hammock への実関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory
variable (C : Type v) [EnrichedCategory SSet.{u} C]

def exInfinityEnrichedUnit :
    EnrichedFunctor SSet.{u} C (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.{u} C) where
  obj X := X
  map X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (X ⟶[SSet.{u}] Y)
  map_id X := by
    change eId (C := C) SSet.{u} X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (X ⟶[SSet.{u}] X) =
      Functor.LaxMonoidal.ε _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (eId (C := C) SSet.{u} X)
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (eId (C := C) SSet.{u} X)
    have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (𝟙_ SSet.{u}) = Functor.LaxMonoidal.ε _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity := by
      simpa using (NatTrans.IsMonoidal.unit (τ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.{u}))
    exact h.trans (congrArg (fun z => z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (eId (C := C) SSet.{u} X)) hu)
  map_comp X Y Z := by
    change eComp (C := C) SSet.{u} X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (X ⟶[SSet.{u}] Z) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (X ⟶[SSet.{u}] Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (Y ⟶[SSet.{u}] Z)) ≫
        Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (eComp (C := C) SSet.{u} X Y Z)
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (eComp (C := C) SSet.{u} X Y Z)
    have hμ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app ((X ⟶[SSet.{u}] Y) ⊗ Y ⟶[SSet.{u}] Z) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (X ⟶[SSet.{u}] Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (Y ⟶[SSet.{u}] Z)) ≫
          Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _ _ := by
      simpa using (NatTrans.IsMonoidal.tensor (τ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.{u})
        (X := X ⟶[SSet.{u}] Y) (Y := Y ⟶[SSet.{u}] Z))
    exact h.trans ((congrArg (fun z => z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
      (eComp (C := C) SSet.{u} X Y Z)) hμ).trans (Category.assoc _ _ _))

lemma exInfinityEnrichedUnit_map (X Y : C) :
    (exInfinityEnrichedUnit C).map X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (X ⟶[SSet.{u}] Y) := rfl

end SerrePositivity.EInfinity.Hammock
