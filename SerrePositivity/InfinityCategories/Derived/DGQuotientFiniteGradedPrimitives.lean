module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaClosedRightShift
public import SerrePositivity.InfinityCategories.Derived.DGQuotientFiniteShiftedPrimitives

/-! # 共通実分母による元の斉次 Hom の有限個の障害の零化

概要：シフトされた比較の核にある元の斉次閉元の有限族を、元の dg Hom の境界にする。
方針：shift 閉射の共通分母と Hom end の原始元を、斉次射影と Yoneda 逆写像で戻す。
規約：次数は互いに異なってよい。使われ方：実 pinched 境界の斉次障害の相対零化。
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

/-- 全次数の有限個の斉次障害に、共通実分母と元の dg Hom の実原始元が存在する。 -/
theorem dgQuotientFiniteGraded_exists_primitives (P : Set D) (hP : localKFlat A D P)
    {m : ℕ} (x : D) (y : Fin m → D) (n : Fin m → ℤ)
    (f : ∀ i, GradedHom A x (y i) (n i)) (hc : ∀ i, differential A (f i) = 0)
    (hf : ∀ i, (moduleToDerived A D).map
      (dgYonedaClosedRightShift A D (n i) (f i) (hc i) ≫
        (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) (y i))⟦n i⟧')
          = 0) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex q) (Simplex.vertex x)), s.edge ∈ dgVerdierEdges A D P ∧
      ∀ i, ∃ h : GradedHom A q (y i) (n i - 1),
        (homObject A D q (y i)).d (n i - 1) (n i) h =
          compose A (f i) (closedHomEquiv A D _ _ (edgeClosed s)).val (zero_add (n i)) := by
  obtain ⟨q, s, hs, hp⟩ := dgQuotientFiniteShifted_exists_primitives A D P hP x y n
    (fun i => dgYonedaClosedRightShift A D (n i) (f i) (hc i)) hf
  refine ⟨q, s, hs, fun i => ?_⟩
  obtain ⟨h, hh⟩ := hp i
  have he := dgYonedaClosedRightShift_precompose_cycle A D (q := q) (x := x) (y := y i)
    (n i) (f i) (hc i) (edgeClosed s)
  exact dgYonedaRightShift_exists_primitive A D (n i) (n i - 1) (by omega) _ h (hh.trans he)

end SerrePositivity.InfinityCategories
