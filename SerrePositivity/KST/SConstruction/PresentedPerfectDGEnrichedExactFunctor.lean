module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGExactFamily
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity

/-! # 全高次入力を保つ厳密豊穣完全 Perf 関手
概要：元の厳密 dg 入力圏から、安定 ∞ 圏と完全関手の単体的圏への豊穣関手を与える。
方針：完全関手空間の実 core への持ち上げに、元の関手族の単位・合成等式を反映する。
規約：全 native Kan 入力と全 Hom を保持。使われ方：S•・実現・BF の豊穣作用への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ実安定値を、完全関手空間の core で豊穣化した圏の対象として使う。 -/
def presentedPerfectDGStableQCat (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{max (u + 1) v} :=
  show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory from presentedPerfectDGStableCategory A C

/-- 元の全 native Kan 関手族を保持する、安定 ∞ 圏への厳密単体的豊穣 Perf 関手。 -/
def presentedPerfectDGEnrichedExactFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{max (u + 1) v} where
  obj := presentedPerfectDGStableQCat A
  map C D := presentedPerfectDGExactCoreFamilyMap A C D
  map_id C := by
    ext n x
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun f => f.app n x) (presentedPerfectDGNativeFamilyMap_unit A C)
  map_comp C D E := by
    ext n p
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun f => f.app n p) (presentedPerfectDGNativeFamilyMap_comp A C D E).symm

/-- 完全性を忘れる二つの包含の後で、元の全単体的 Perf 関手族を回収する。 -/
lemma presentedPerfectDGEnrichedExactFunctor_family (C D : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGEnrichedExactFunctor A).map C D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
        (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) :
          SSet.{max (u + 1) v})).ι) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
            (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D)).ι =
      presentedPerfectDGNativeFamilyMap A C D :=
  presentedPerfectDGExactCoreFamilyMap_inclusion A C D

end SerrePositivity.KST.SConstruction
