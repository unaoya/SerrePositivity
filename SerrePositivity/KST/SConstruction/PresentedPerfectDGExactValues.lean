module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionExact
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInfinityStableValues
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories

/-! # 厳密 dg 入力の実安定値と完全射
概要：元の豊穣 Perf 関手の実値と通常の入力射を、安定 ∞ 圏と完全関手に束ねる。
方針：同じラベル付き native nerve と同じ dg 作用を保持し、証明済みの完全性を付ける。
規約：完全関手空間の高次単体は後続で持ち上げる。使われ方：厳密豊穣 Perf の値域。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元のラベル付き Perf の実 native nerve を、同じ小さい安定 ∞ 圏として保持する。 -/
def presentedPerfectDGStableCategory (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} :=
  ⟨(presentedPerfectDGQCat A C).obj, inferInstance, presentedPerfectDGQCat_isStable A C⟩

/-- 安定値の底は、元の豊穣 Perf 関手と同じ全 native 単体集合。 -/
lemma presentedPerfectDGStableCategory_obj (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGStableCategory A C).obj = (presentedPerfectDGQCat A C).obj := rfl

/-- 元の厳密 dg 入力射による同じラベル作用を、完全射として束ねる。 -/
def presentedPerfectDGExactMap {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
      (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A C D F.down),
    presentedPerfectDGActionNerve_isExactFunctor A C D F.down⟩

/-- 元の通常の Perf 射は、同じ native 作用の完全射である。 -/
lemma presentedPerfectDGQCatFunctor_map_isExactFunctor
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((presentedPerfectDGQCatFunctor A).map F) :=
  presentedPerfectDGActionNerve_isExactFunctor A C D F.down

/-- 元の厳密 dg 射の恒等・合成を保つ、安定 ∞ 圏と完全射への通常の Perf 関手。 -/
def presentedPerfectDGStableCategoryFunctor :
    PerfDGInput.{u, v} A ⥤ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} where
  obj := presentedPerfectDGStableCategory A
  map := presentedPerfectDGExactMap A
  map_id C := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext
    exact (presentedPerfectDGQCatFunctor A).map_id C
  map_comp F G := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext
    exact (presentedPerfectDGQCatFunctor A).map_comp F G

end SerrePositivity.KST.SConstruction
