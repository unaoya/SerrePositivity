module
public import SerrePositivity.KST.SConstruction.SExactEnrichedFunctor
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.CoreEnrichedFunctor

/-! # 自然同値の全 core を保つ厳密豊穣 S_n
概要：実 S_n の豊穣自己関手を、安定 ∞ 圏と完全関手の局所 Kan な単体的圏へ移す。
方針：元の全 Hom 作用に実 core 関手を適用し、元の単位・合成等式を保持する。
規約：全高次自然同値を保持する。使われ方：厳密 dg Perf 入力との豊穣合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 実 core の豊穣単位射は、包含後に同じ元の完全射の単位射を回収する。 -/
lemma stableExactCoreHomEquiv_inclusion {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    eHomEquiv SSet.{u} F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})).ι =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F) ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnit ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (𝟙_ SSet.{u})).ι = 𝟙 _ := rfl
  rw [← Category.assoc, h, Category.id_comp]

/-- 元の S_n の全高次自然同値を保持する、StableQCat の厳密豊穣自己関手。 -/
def sExactCoreEnrichedEndofunctor (n : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor (sExactEnrichedEndofunctor n)

/-- core の包含後には、元の全単体的な完全関手空間への作用を回収する。 -/
lemma sExactCoreEnrichedEndofunctor_inclusion (n : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (sExactCoreEnrichedEndofunctor n).map C D ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (sExactCategory n C) (sExactCategory n D) : SSet.{u})).ι =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})).ι ≫ sExactEnrichedMap n C D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι _

/-- 元の core 豊穣作用は、同じ元の cofiber 型 S_n 完全射を回収する。 -/
lemma sExactCoreEnrichedEndofunctor_hom (n : ℕ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    eHomEquiv SSet.{u} F ≫ (sExactCoreEnrichedEndofunctor n).map C D =
      eHomEquiv SSet.{u} (show (sExactCoreEnrichedEndofunctor n).obj C ⟶
        (sExactCoreEnrichedEndofunctor n).obj D from sExactMap n F) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (sExactCategory n C) (sExactCategory n D) : SSet.{u})).ι).mp
  erw [Category.assoc, sExactCoreEnrichedEndofunctor_inclusion, ← Category.assoc,
    stableExactCoreHomEquiv_inclusion, sExactEnrichedEndofunctor_hom,
    stableExactCoreHomEquiv_inclusion]
  rfl

end SerrePositivity.KST.SConstruction
