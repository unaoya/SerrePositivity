module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEnrichedExactFunctor

/-! # 厳密豊穣完全 Perf 関手の元の通常射の回収
概要：完全関手空間への精密化は、同じ元の厳密 dg 入力射の像を保持する。
方針：二つの実包含の後で元の curry を回収し、包含の単射性で豊穣単位射を同定する。
規約：単位・合成だけで通常射の回収を省略しない。使われ方：元の dgK との比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

private lemma stableQCat_homEquiv_inclusion
    {X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{w}} (f : X ⟶ Y) :
    eHomEquiv SSet.{w} f ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Y : SSet.{w})).ι ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Y).ι) = curry' (C := SSet.{w}) f.hom := by
  have h : eHomEquiv SSet.{w} f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Y : SSet.{w})).ι =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv f := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv f) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]
    have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnit ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (𝟙_ SSet.{w})).ι = 𝟙 _ := rfl
    rw [← Category.assoc, hu, Category.id_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g : 𝟙_ SSet.{w} ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Y : SSet.{w}) =>
      g ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Y).ι) h).trans
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι f))

/-- 包含後の豊穣単位射の作用は、同じ元の完全な Perf 射の curry を回収する。 -/
lemma presentedPerfectDGEnrichedExactFunctor_hom_recovery
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (eHomEquiv SSet.{max (u + 1) v} F ≫ (presentedPerfectDGEnrichedExactFunctor A).map C D) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
        (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) :
          SSet.{max (u + 1) v})).ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
            (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D)).ι) =
      curry' (C := SSet.{max (u + 1) v}) (presentedPerfectDGExactMap A F).hom := by
  change (perfDGInputUnitHomEquiv A C D F ≫ presentedPerfectDGExactCoreFamilyMap A C D) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
      (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) :
        SSet.{max (u + 1) v})).ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
          (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D)).ι) = _
  rw [Category.assoc, ← Category.assoc (presentedPerfectDGExactCoreFamilyMap A C D),
    presentedPerfectDGExactCoreFamilyMap_inclusion]
  change perfDGInputUnitHomEquiv A C D F ≫ presentedPerfectDGNativeFamilyMap A C D = _
  rw [perfDGInputUnitHomEquiv_point, presentedPerfectDGNativeFamilyMap_fixed]
  rfl

/-- 元の入力射での豊穣作用は、同じ元の完全な dg Perf 射の豊穣表示に一致する。 -/
lemma presentedPerfectDGEnrichedExactFunctor_hom
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫ (presentedPerfectDGEnrichedExactFunctor A).map C D =
      eHomEquiv SSet.{max (u + 1) v}
        (show presentedPerfectDGStableQCat A C ⟶ presentedPerfectDGStableQCat A D from
          presentedPerfectDGExactMap A F) := by
  apply (cancel_mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
    (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) :
      SSet.{max (u + 1) v})).ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
        (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D)).ι)).mp
  exact (presentedPerfectDGEnrichedExactFunctor_hom_recovery A F).trans
    (stableQCat_homEquiv_inclusion (show presentedPerfectDGStableQCat A C ⟶
      presentedPerfectDGStableQCat A D from presentedPerfectDGExactMap A F)).symm

end SerrePositivity.KST.SConstruction
