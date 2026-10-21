module
public import SerrePositivity.KST.SConstruction.CoordinateEnrichedAssembly
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMultiRealizationAction

/-! # 元の反復組み立てと全 native dg 入力族
概要：一次方向を固定した実現への全作用と、元の区間組み立ての厳密自然性を与える。
方針：実 core 多単体図式の全高次比較に一般の座標組み立て定理を適用する。
規約：元の区間と全 gapped 図式を保持する。使われ方：境界商上の BF 構造写像。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の一次方向を固定した実現に対する、全 native dg 入力族の実作用。 -/
def presentedPerfectDGOneDirectionAction (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    (oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C)) ⊗
        (C ⟶[SSet.{max (u + 1) v}] D) ⟶
    (oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A D)) :=
  coordinateEnrichedDiagonalAction (presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1))
    (multiIndexDiagonal r ⋙ oneDirectionIndex r) C D

/-- 元の区間組み立ては、全 native dg パラメータ作用と厳密に可換する。 -/
lemma presentedPerfectDGMultiDiagonalAssembly_action (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (multiDiagonalAssembly r (stableCategoryModel (presentedPerfectDGStableCategory A C)) ▷
      (C ⟶[SSet.{max (u + 1) v}] D)) ≫
      presentedPerfectDGMultiRealizationAction A (r + 1) C D =
    (α_ (Δ[1] : SSet.{max (u + 1) v})
      ((oneDirectionRealizationFunctor r).obj
        (stableCategoryModel (presentedPerfectDGStableCategory A C)))
      (C ⟶[SSet.{max (u + 1) v}] D)).hom ≫
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ presentedPerfectDGOneDirectionAction A r C D) ≫
      multiDiagonalAssembly r (stableCategoryModel (presentedPerfectDGStableCategory A D)) :=
  coordinateDiagonalAssembly_enriched_naturality r
    (presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1)) C D

end SerrePositivity.KST.SConstruction
