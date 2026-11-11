module
public import SerrePositivity.KST.Fibration.StableCoreSingleKanFunctor
public import SerrePositivity.KST.Fibration.ExInfinityCommSqEdges

/-! # 元の core S 座標同型を、同じ Ex∞ Kan 値と元の完全射の座標同型へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction

open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ元の SSet 座標の等号は、Ex∞ 後にも元の等号による Kan 射へ送られる。 -/
theorem exInfinityKan_eqToHom {A B : SSet.{u}} (h : A = B) :
    eqToHom (congrArg (fun V : SSet.{u} => exInfinityClosedKanEnrichedFunctor.obj ⟨V⟩) h) =
      exInfinityKanMap (eqToHom h) := by
  cases h
  change (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj A)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (𝟙 A)
  exact (CategoryTheory.Functor.map_id _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity A).symm

/-- 元の core S の座標同型の同じ Ex∞ 像を、Kan 値の座標同型として保持する。 -/
def coreSingleKanIso (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    stableCoreSingleKanObject C ≅ (stableMultiKanEnrichedFunctor 0).obj C where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSingleRealizationIso (stableCategoryModel C)).hom
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSingleRealizationIso (stableCategoryModel C)).inv
  hom_inv_id := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- 同じ Kan 座標同型の前向き射は、元の対象座標の等号による射そのもの。 -/
theorem coreSingleKanIso_hom_eq (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (coreSingleKanIso C).hom = eqToHom (stableCoreSingleKan_object_eq C).symm := by
  change exInfinityKanMap (coreSingleRealizationIso (stableCategoryModel C)).hom = _
  rw [coreSingleRealizationIso_hom_eq]
  exact (exInfinityKan_eqToHom (coreSingleRealization_obj_eq (stableCategoryModel C))).symm

/-- 同じ Kan 座標同型の逆射も、元の逆向きの対象座標の等号による射そのもの。 -/
theorem coreSingleKanIso_inv_eq (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (coreSingleKanIso C).inv = eqToHom (stableCoreSingleKan_object_eq C) := by
  have he : coreSingleKanIso C = eqToIso (stableCoreSingleKan_object_eq C).symm :=
    Iso.ext (coreSingleKanIso_hom_eq C)
  rw [he]
  rfl

/-- 同じ元の完全射を保った、Ex∞ 後の座標同型の自然性。 -/
theorem coreSingleKanIso_naturality {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (f : C ⟶ D) :
    exInfinityKanMap (simplicialDiagonalFunctor.map (coreSExactMap f)) ≫
        (coreSingleKanIso D).hom =
      (coreSingleKanIso C).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
        ((multiRealizationFunctor 1).map (stableExactInputMap f)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    coreSExactMap_realization_eq, coreSingleRealizationIso_naturality]

end SerrePositivity.KST.Fibration
