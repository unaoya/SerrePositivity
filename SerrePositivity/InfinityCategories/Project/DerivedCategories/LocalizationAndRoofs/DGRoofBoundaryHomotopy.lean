module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofHomComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientRoofFiniteFillers

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped _root_.Simplicial

/-- 全境界上で定値の実ホモトピーの二端点は、境界への制限で厳密に一致する。 -/
lemma RoofBoundaryFixedHomotopy.boundary_eq {X : SSet.{u}} {n : ℕ} {f g : Δ[n] ⟶ X}
    (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy f g) : (∂Δ[n]).ι ≫ f = (∂Δ[n]).ι ≫ g := by
  have h := congrArg (fun k => SSet.ι₁ ≫ k) H.boundary
  rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.homotopy.h₁,
    ← Category.assoc, SSet.ι₁_fst, Category.id_comp] at h
  exact h.symm

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 指定閉分母の固定 fiber の境界固定比較を、元の像への実屋根比較に移す。 -/
def dgClosedRoofRelativeHomotopy (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) {n : ℕ}
    (f : Δ[n] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
    (g : Δ[n] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy f
      (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s)
      (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) where
  homotopy := {
    h := H.homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s
    h₀ := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s) H.homotopy.h₀)
    h₁ := by
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s)
          H.homotopy.h₁)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun h => g ≫ h) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_comparison A D P x y s).symm))
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      exact False.elim a.1.2 }
  boundary := by
    change _ ≫ (H.homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s) = _
    rw [← Category.assoc, H.boundary, Category.assoc, Category.assoc]

/-- 固定 fiber から写した比較は、全ホモトピー上で指定実分母に厳密に定値。 -/
lemma dgClosedRoofRelativeHomotopy_projection (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) {n : ℕ}
    (f : Δ[n] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
    (g : Δ[n] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy f
      (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y))) :
    (dgClosedRoofRelativeHomotopy A D P x y s f g H).homotopy.h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s) := by
  change (H.homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
