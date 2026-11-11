module
public import SerrePositivity.KST.SConstruction.PerfDGInputSimplicial
public import SerrePositivity.KST.SConstruction.KanSourceCoreMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial

/-! # 元の全 native 関手族を保つ実 Perf の厳密単体的豊穣関手
概要：出力宇宙の厳密 dg 入力から、ラベル付き Perf の native nerve を QCat 値に構成する。
方針：実関手族を core へ持ち上げ、元の全単体的合成・単位保存を包含で反映する。
規約：元の高次入力と実 Perf の対象宇宙を保持。使われ方：完全性と BF K への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元のラベル付き Perf の native nerve を、同じ宇宙の QCat 対象として保持する。 -/
def presentedPerfectDGQCat (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{max (u + 1) v} :=
  show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject from
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C), inferInstance⟩

/-- 元の実 QCat 値の底の native Perf 単体集合は quasicategory。 -/
instance presentedPerfectDGQCat_obj_quasicategory (C : PerfDGInput.{u, v} A) :
    Quasicategory (presentedPerfectDGQCat A C).obj := by
  change Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C))
  infer_instance

/-- 元の全 native Kan 入力から、実 Perf 関手空間の core への射。 -/
def presentedPerfectDGNativeCoreFamilyMap (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGNativeParameter A C D ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C))).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D))) : SSet) :=
  kanSourceCoreMap (presentedPerfectDGNativeFamilyMap A C D)

/-- 実 core 関手族は、包含後に元の全単体的関手族を厳密に回収する。 -/
lemma presentedPerfectDGNativeCoreFamilyMap_inclusion (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGNativeCoreFamilyMap A C D ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C))).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)))).ι =
      presentedPerfectDGNativeFamilyMap A C D := rfl

/-- 元の厳密 dg 圏と全 native 関手族から QCat への、実 Perf の厳密単体的豊穣関手。 -/
def presentedPerfectDGEnrichedFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{max (u + 1) v} where
  obj := presentedPerfectDGQCat A
  map C D := presentedPerfectDGNativeCoreFamilyMap A C D
  map_id C := by
    ext n x
    apply Subtype.ext
    exact congrArg (fun f => f.app n x) (presentedPerfectDGNativeFamilyMap_unit A C)
  map_comp C D E := by
    ext n p
    apply Subtype.ext
    exact congrArg (fun f => f.app n p) (presentedPerfectDGNativeFamilyMap_comp A C D E).symm

end SerrePositivity.KST.SConstruction
