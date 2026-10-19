module
public import SerrePositivity.InfinityCategories.Derived.DGRestrictionShiftedBoundary
public import SerrePositivity.InfinityCategories.Derived.DGQuotientFiniteGradedPrimitives

/-! # 商で境界となる有限個の斉次閉元の共通実分母による零化

概要：商で境界となる元の斉次閉元の有限族を、一つの元の実分母で同時に境界にする。
方針：商の原始元からシフト比較の導来零性を得て、元の Hom の原始元の回収へ渡す。
規約：次数は任意の整数。使われ方：β3 の pinched Hom の相対高次障害の零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 商で境界となる有限族は、共通実分母の後で既に元の dg Hom の境界となる。 -/
theorem dgQuotientFiniteBoundary_exists_primitives (P : Set D) (hP : localKFlat A D P)
    {m : ℕ} (x : D) (y : Fin m → D) (n : Fin m → ℤ)
    (f : ∀ i, GradedHom A x (y i) (n i)) (hc : ∀ i, differential A (f i) = 0)
    (hb : ∀ i, ∃ b : GradedHom A ((inclusion A D P).obj x)
      ((inclusion A D P).obj (y i)) (n i - 1),
      (homObject A (QuotientObject D P) ((inclusion A D P).obj x)
        ((inclusion A D P).obj (y i))).d (n i - 1) (n i) b =
          ((inclusion A D P).map x (y i)).f (n i) (f i)) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex q) (Simplex.vertex x)), s.edge ∈ dgVerdierEdges A D P ∧
      ∀ i, ∃ h : GradedHom A q (y i) (n i - 1),
        (homObject A D q (y i)).d (n i - 1) (n i) h =
          compose A (f i) (closedHomEquiv A D _ _ (edgeClosed s)).val (zero_add (n i)) := by
  apply dgQuotientFiniteGraded_exists_primitives A D P hP x y n f hc
  intro i
  exact dgRestrictionShiftedComparison_zero_of_boundary A D (QuotientObject D P)
    (inclusion A D P) (n i) (n i - 1) (by omega) (f i) (hc i) (hb i)

end SerrePositivity.InfinityCategories
