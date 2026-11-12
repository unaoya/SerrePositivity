module
public import SerrePositivity.KST.Fibration.VerdierFullSZeroCornerNativeCoordinates

/-!
概要：全 S• 零値作用を、元の native 正反復 Kan 対象の全 Hom へ照合する。
方針：同じ core S 座標同型で標的を輸送し、始域の実 core 包含で元の作用を回収する。
規約：元の全高次族・実包含・指定完全関手の点を保持する。
使われ方：指定 Verdier 二胞体の長 Hom を保持する中間対象比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

/-- 元の native 標的座標を使う、同じ全 S• 零値関手族。 -/
def zeroFunctorFullSNativeKanFamily (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    zeroFunctorLocus A C ⟶
      (ihom (fullSRealizationKanObject A).obj).obj ((stableMultiKanEnrichedFunctor 0).obj C).obj :=
  zeroFunctorFullSKanFamily A C ≫
    (ihom (fullSRealizationKanObject A).obj).map (coreSingleKanIso C).hom

/-- 同じ全族を元の native core 包含で制限すると、元の全 native Hom 作用そのもの。 -/
theorem zeroFunctorFullSNativeKanFamily_core (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    zeroFunctorFullSNativeKanFamily A C ≫
        (pre (C := SSet.{u}) (fullSNativeCoreInclusion A)).app
          ((stableMultiKanEnrichedFunctor 0).obj C).obj =
      zeroFunctorLocusToStableHom A C ≫ (stableMultiKanEnrichedFunctor 0).map A C := by
  apply uncurry_injective
  rw [uncurry_pre_app, zeroFunctorFullSNativeKanFamily, uncurry_natural_right]
  have hc := congrArg (uncurry (C := SSet.{u})) (zeroFunctorFullSKanFamily_core A C)
  rw [uncurry_pre_app] at hc
  change ((show ((stableMultiKanEnrichedFunctor 0).obj A).obj ⟶
    (fullSRealizationKanObject A).obj from fullSNativeCoreInclusion A) ▷ _) ≫
    (uncurry (zeroFunctorFullSKanFamily A C) ≫ (coreSingleKanIso C).hom) = _
  erw [fullSNativeCoreInclusion, comp_whiskerRight, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion A) ▷ _), hc]
  conv_lhs => erw [stableCoreSingleKanFamily_coordinates (zeroFunctorLocusToStableHom A C)]
  have hA : (show ((stableMultiKanEnrichedFunctor 0).obj A).obj ⟶
      (stableCoreSingleKanObject A).obj from (coreSingleKanIso A).inv) ≫
        (coreSingleKanIso A).hom = 𝟙 ((stableMultiKanEnrichedFunctor 0).obj A).obj :=
    (coreSingleKanIso A).inv_hom_id
  have hC : (show ((stableMultiKanEnrichedFunctor 0).obj C).obj ⟶
      (stableCoreSingleKanObject C).obj from (coreSingleKanIso C).inv) ≫
        (coreSingleKanIso C).hom = 𝟙 ((stableMultiKanEnrichedFunctor 0).obj C).obj :=
    (coreSingleKanIso C).inv_hom_id
  simp only [Category.assoc]
  erw [← Category.assoc ((show ((stableMultiKanEnrichedFunctor 0).obj A).obj ⟶
    (stableCoreSingleKanObject A).obj from (coreSingleKanIso A).inv) ▷ _), ← comp_whiskerRight,
    hA, id_whiskerRight, Category.id_comp, hC, Category.comp_id]

/-- 同じ元の指定点では、元の全 S• 射の native 標的座標への実像を回収する。 -/
theorem zeroFunctorFullSNativeKanFamily_fixed {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    zeroFunctorParameterPoint F hF ≫ zeroFunctorFullSNativeKanFamily A C =
      curry' (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (zeroFunctorFullSMap F hF)) ≫
        (show (stableCoreSingleKanObject C).obj ⟶ ((stableMultiKanEnrichedFunctor 0).obj C).obj from
          (coreSingleKanIso C).hom)) := by
  rw [zeroFunctorFullSNativeKanFamily, ← Category.assoc, zeroFunctorFullSKanFamily_fixed]
  exact curry'_ihom_map _ _

end SerrePositivity.KST.Fibration
