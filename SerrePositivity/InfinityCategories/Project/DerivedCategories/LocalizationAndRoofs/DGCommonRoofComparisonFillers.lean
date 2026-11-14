module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGCommonRoofRefinementFillers

/-! # 共通宇宙の元の屋根比較の局所有限相対充填

概要：商側屋根の指定係数単体を、同じ元の添字からの共通細分後で相対的に持ち上げる。
方針：元の始域で有限充填を行い、分母を合成して AsSmall へ移す。
規約：固定商 Hom への逆写像を選ばない。使われ方：全空間比較の局所充填条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 商側屋根の有限指定係数単体を、同じ添字からの一つの細分後で相対充填する。 -/
theorem dgCommonRoofComparison_relative_fillers (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonRoofIndex A D P x)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofOriginal A D P x (y i)).obj c)
    (g : ∀ i, ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofQuotient A D P x (y i)).obj c) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofComparison A D P x (y i)).app c =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i)) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonRoofIndex A D P x, ∃ r : c ⟶ d,
      ∃ t : ∀ i, ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofOriginal A D P x (y i)).obj d) _⦋n + 1⦌,
        (∀ i, (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (t i) =
          b i ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofOriginal A D P x (y i)).map r) ∧
        ∀ i, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofQuotient A D P x (y i)).map r)
          (SSet.yonedaEquiv.symm (t i) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofComparison A D P x (y i)).app d)) := by
  cases c with | up c =>
    let s := c.unop
    let q := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left
    obtain ⟨p, r, hr, t, ht, hh⟩ :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_actualRelativeHomotopies A D P hP q y b g hb
    let d := op (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefine A D P x s r hr)
    let R := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefineHom A D P x s r hr).op
    refine ⟨AsSmall.up.obj d, AsSmall.up.map R, fun i => (t i).toPinched, ht, ?_⟩
    intro i
    let H := Classical.choice (hh i)
    change Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy
      (SSet.yonedaEquiv.symm (g i) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap _)
      (SSet.yonedaEquiv.symm (t i).toPinched ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap _))
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap_yoneda, SSet.yonedaEquiv_symm_comp]
    exact ⟨⟨H.homotopy, H.boundary⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
