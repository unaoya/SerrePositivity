module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblySpan
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionKanEquivalence
public import SerrePositivity.KST.SConstruction.SuspensionLocalizedEquivalence

/-! # 元の Kan 隣接段 span の左脚の局所化可逆性
概要：同じ元の Kan S₁ 比較の suspension である実左脚が、局所化で可逆であると示す。
方針：元の全基点 π 同型から点つき Whitehead を適用し、元の suspension 作用を使う。
規約：自然な逆や ModelCategory 引数は追加しない。使われ方：BF の homotopy pushout 段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 元の同じ左脚は、追加仮定なしに anodyne 局所化で可逆。 -/
lemma presentedPerfectDGKanAssemblyLeftMap_localized_isIso (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
        ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
          presentedPerfectDGKanAssemblyLeftMap A r C).right) := by
  erw [presentedPerfectDGKanAssemblyLeftMap_eq]
  exact suspensionImage_isIso_of_piIsomorphism AnodyneHomotopy.anodyneQ
    (Localization.inverts _ anodyneExtensions)
    (presentedPerfectDGOneDirectionKanComparisonMap A r C).hom
    (presentedPerfectDGOneDirectionKanComparisonMap_piIsomorphism A r C)

end SerrePositivity.KST.SConstruction
