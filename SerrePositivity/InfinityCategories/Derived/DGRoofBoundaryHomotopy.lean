module
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofHomComparison
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRoofFiniteFillers

/-! # 固定 fiber の境界固定ホモトピーを実屋根へ移す

概要：商 Hom 内の比較を、元の実屋根の商像への境界固定の実ホモトピーへ写す。
方針：指定閉分母の商 Hom 包含で後合成し、全次数の比較四角形で終端を照合する。
規約：境界上の定値性を厳密に保持する。使われ方：有限相対充填の実屋根への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定閉分母の固定 fiber の境界固定比較を、元の像への実屋根比較に移す。 -/
def dgClosedRoofRelativeHomotopy (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) {n : ℕ}
    (f : Δ[n] ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
      ((DGQuotient.inclusion A D P).obj y))
    (g : Δ[n] ⟶ DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (H : RoofBoundaryFixedHomotopy f
      (g ≫ pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (Complex A) s.obj.left) y))) :
    RoofBoundaryFixedHomotopy (f ≫ dgQuotientClosedRoofHomInclusion A D P x y s)
      (g ≫ dgClosedRoofHomInclusion A D P x y s ≫ dgRoofCorrespondenceMap A D P x y) where
  homotopy := {
    h := H.homotopy.h ≫ dgQuotientClosedRoofHomInclusion A D P x y s
    h₀ := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ dgQuotientClosedRoofHomInclusion A D P x y s) H.homotopy.h₀)
    h₁ := by
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ dgQuotientClosedRoofHomInclusion A D P x y s)
          H.homotopy.h₁)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun h => g ≫ h) (dgClosedRoofHomInclusion_comparison A D P x y s).symm))
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      exact False.elim a.1.2 }
  boundary := by
    change _ ≫ (H.homotopy.h ≫ dgQuotientClosedRoofHomInclusion A D P x y s) = _
    rw [← Category.assoc, H.boundary, Category.assoc, Category.assoc]

end SerrePositivity.InfinityCategories
