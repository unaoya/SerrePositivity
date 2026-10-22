module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyRight
public import SerrePositivity.KST.SConstruction.ExInfinitySuspensionAssemblyUnit

/-! # 同じ隣接段の右脚と元の組み立ての単位上の回収
概要：新しい前向き右脚が、元の suspension 単位上で同じ元の組み立てを回収する。
方針：同じ Ex∞ 比較の単位条件と、写した元の組み立ての単位自然性を合成する。
規約：比較の逆・単射性は使わない。使われ方：元の BF 構造射との比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の一次方向商の同じ Ex∞ 単位を、元の円で suspension した射。 -/
def presentedPerfectDGKanAssemblySourceUnit (r : ℕ) (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj :=
  exInfinitySuspensionUnit ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)

/-- 新しい実右脚は、元の同じ単位の suspension 上で元の組み立てを厳密に回収する。 -/
lemma presentedPerfectDGKanAssemblyRightMap_unit (r : ℕ) (C : PerfDGInput.{u, v} A) :
    presentedPerfectDGKanAssemblySourceUnit A r C ≫
      (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
        ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
          presentedPerfectDGKanAssemblyRightMap A r C) =
    (show ((presentedPerfectDGAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGBoundaryPointedEnrichedFunctor A (r + 1)).obj C).obj from
        presentedPerfectDGAssemblyMap A r C) ≫
      exInfinityPointedUnit ((presentedPerfectDGBoundaryPointedEnrichedFunctor A (r + 1)).obj C) :=
  exInfinitySuspensionAssembly_unit
    (X := (presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)
    (Y := (presentedPerfectDGBoundaryPointedEnrichedFunctor A (r + 1)).obj C)
    (presentedPerfectDGAssemblyMap A r C)

end SerrePositivity.KST.SConstruction
