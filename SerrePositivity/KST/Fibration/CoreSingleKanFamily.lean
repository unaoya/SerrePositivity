module
public import SerrePositivity.KST.Fibration.CoreSingleRealizationFamily
public import SerrePositivity.KST.Fibration.CoreSingleKanCoordinates
public import SerrePositivity.KST.SConstruction.CoaugmentedTensorStrength

/-!
概要：元の core S 実現の全入力族を、同じ Ex∞ Kan 対象と評価へ移す。
方針：対象等号による評価の輸送と、元の Ex∞ の全 Hom 作用を照合する。
規約：全パラメータを保持し、指定二胞体の比較は別途証明する。
使われ方：商核零化円柱と指定 Verdier 四角形との全 Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction

open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private theorem relabelKan_uncurry {C : Type v} [EnrichedCategory SSet.{u} C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (obj : C → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (h : F.obj = obj) {X Y : C} {P : SSet.{u}} (H : P ⟶ (X ⟶[SSet.{u}] Y)) :
    uncurry (H ≫ (relabelEnrichedObjects F obj h).map X Y) =
      (eqToHom (congrArg (fun k : C → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} => (k X).obj) h).symm ▷ P) ≫
        uncurry (H ≫ F.map X Y) ≫
          eqToHom (congrArg (fun k : C → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} => (k Y).obj) h) := by
  cases h
  simp only [relabelEnrichedObjects, eqToHom_refl, Category.comp_id,
    id_whiskerRight, Category.id_comp]

/-- 全入力族の Kan 評価は、元の Kan 座標同型で挟んだ同じ単回実現作用。 -/
theorem stableCoreSingleKanFamily_coordinates {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C)) :
    uncurry (H ≫ stableCoreSingleKanEnrichedFunctor.map A C) =
      ((show (stableCoreSingleKanObject A).obj ⟶
          ((stableMultiKanEnrichedFunctor 0).obj A).obj from (coreSingleKanIso A).hom) ▷ P) ≫
        uncurry (H ≫ (stableMultiKanEnrichedFunctor 0).map A C) ≫
          (coreSingleKanIso C).inv := by
  change uncurry (H ≫ (relabelEnrichedObjects (stableMultiKanEnrichedFunctor 0)
    stableCoreSingleKanObject (funext stableCoreSingleKan_object_eq)).map A C) = _
  rw [relabelKan_uncurry, coreSingleKanIso_hom_eq, coreSingleKanIso_inv_eq]
  rfl

/-- core S 実現の全 Hom を Ex∞ へ送ると、元の Kan 値の豊穣関手そのもの。 -/
theorem coreSingleRealizationKanEnrichedFunctor_eq :
    coreSingleRealizationEnrichedFunctor.comp SSet exInfinityClosedKanEnrichedFunctor =
      stableCoreSingleKanEnrichedFunctor.{u} := by
  rw [stableCoreSingleKanEnrichedFunctor_eq]
  change (relabelEnrichedObjects (stableMultiRealizationEnrichedFunctor 1)
    coreSingleRealizationObject (funext coreSingleRealizationObject_eq)).comp SSet
      exInfinityClosedKanEnrichedFunctor = _
  rw [relabelEnrichedObjects_eq]
  rfl

/-- 同じ元の core S 座標で、全 Hom の Ex∞ 作用を厳密に回収する。 -/
theorem coreSingleRealizationKan_map (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    coreSingleRealizationEnrichedFunctor.map A C ≫
        exInfinityClosedKanEnrichedFunctor.map _ _ =
      stableCoreSingleKanEnrichedFunctor.map A C := by
  have hm : ∀ (F G : EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}),
      F = G → HEq (F.map A C) (G.map A C) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (hm _ _ coreSingleRealizationKanEnrichedFunctor_eq)

/-- 全入力族の評価は、同じ元の core S 評価を Ex∞ に送ったものと一致する。 -/
theorem stableCoreSingleKanFamily_action {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C)) :
    uncurry (H ≫ stableCoreSingleKanEnrichedFunctor.map A C) =
      coaugmentedTensorRightStrength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
          (coreSingleRealizationObject A).obj P ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (uncurry (H ≫ coreSingleRealizationEnrichedFunctor.map A C)) := by
  rw [← coreSingleRealizationKan_map, ← Category.assoc]
  exact coaugmentedClosedFamilyMap_strength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit _

/-- 元の商核円柱を Ex∞ に送った全族は、同じ零化族の全閉 Hom 作用である。 -/
theorem quotientSKernelNullCylinder_exInfinity
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    coaugmentedTensorRightStrength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
        (coreSingleRealizationObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A)).obj (Δ[1] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (quotientSKernelNullCylinder h) =
    uncurry ((zeroEndPostcompFamily
      (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
        (verdierSequenceComposite_zero h) ≫
          coreSingleRealizationEnrichedFunctor.map
            (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)) ≫
      exInfinityClosedKanEnrichedFunctor.map _ _) := by
  rw [quotientSKernelNullCylinder_coreRealization]
  exact (coaugmentedClosedFamilyMap_strength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit _).symm

/-- 同じ零化円柱の Ex∞ 像を、元の core S の全 Kan Hom 評価として回収する。 -/
theorem quotientSKernelNullCylinder_coreKan
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    coaugmentedTensorRightStrength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
        (coreSingleRealizationObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A)).obj (Δ[1] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (quotientSKernelNullCylinder h) =
    uncurry (zeroEndPostcompFamily
      (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
        (verdierSequenceComposite_zero h) ≫
          stableCoreSingleKanEnrichedFunctor.map
            (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)) := by
  rw [stableCoreSingleKanFamily_action, quotientSKernelNullCylinder_coreRealization]

end SerrePositivity.KST.Fibration
