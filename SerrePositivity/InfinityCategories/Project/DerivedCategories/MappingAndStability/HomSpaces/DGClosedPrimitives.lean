module
public import SerrePositivity.DifferentialGraded.Category.Basic

/-! # 閉射の H⁰ での零性と具体的な原始元

概要：閉射の零性を、主 Hom 複体の次数 −1 の原始元で判定する。
方針：閉零射の cycle が零であることを線形性から示して境界関係を簡約する。
規約：任意の dg 圏に適用する。使われ方：大きな全加群 end にも同じ証明を適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉零射は主 Hom 複体の零 cycle に対応する。 -/
lemma dgClosedHomEquiv_zero (x y : ClosedCategory A D) :
    closedHomEquiv A D x y (0 : x ⟶ y) = 0 := by
  have h := closedHomEquiv_add A D x y (0 : x ⟶ y) 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

/-- 閉射が H⁰ で零になることと、元の実 Hom 複体での境界性は同値。 -/
lemma dgClosed_zero_iff_primitive {x y : ClosedCategory A D} (f : x ⟶ y) :
    (toHomotopy A D).map f = (toHomotopy A D).map 0 ↔
      ∃ h : (homObject A D x y).X (-1),
        (homObject A D x y).d (-1) 0 h = (closedHomEquiv A D x y f).val := by
  rw [toHomotopy_map_eq_iff_boundary]
  change (∃ h, (homObject A D x y).d (-1) 0 h =
    (closedHomEquiv A D x y f).val - (closedHomEquiv A D x y 0).val) ↔ _
  rw [dgClosedHomEquiv_zero]
  simp only [ZeroMemClass.coe_zero, sub_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
