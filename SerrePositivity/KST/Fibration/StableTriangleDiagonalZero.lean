module
public import SerrePositivity.KST.Fibration.CoherentTriangleDiagonal
public import SerrePositivity.KST.Fibration.StableTriangleZeroHom

/-! # 元の対角一単体を保って、指定二胞体の全長 Hom の零値条件を移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の一単体が表す完全関手の、元の関手圏における実零値条件。 -/
def StableArrowZeroVertex (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌) : Prop :=
  StableHomZeroVertex (a.obj ⟨ULift.up 0⟩) (a.obj ⟨ULift.up 1⟩) (coherentArrowHomVertex a)

/-- 元の直接 path の零値条件は、指定した対角一単体の零値条件そのもの。 -/
theorem stableTriangleDirect_zero_iff (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) :
    StableHomZeroVertex (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)
      (coherentTriangleHomVertex s coherentTriangleDirectPath) ↔
        StableArrowZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s) := Iff.rfl

/-- 直接 path の実零値条件を、同じ指定二胞体の全長 path 族へ移す。 -/
theorem stableTriangleLongHom_zero_of_diagonal (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌)
    (h : StableArrowZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s)) :
    ∀ v, StableHomZeroVertex (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)
      ((coherentTriangleLongHom s).app (Opposite.op ⦋0⦌) v) := by
  intro v
  obtain ⟨p, rfl⟩ := nerveEquiv.symm.surjective v
  exact stableHomZeroVertex_of_edge
    (coherentTriangleHomEdge s (coherentTriangleDirectToPath p))
      ((stableTriangleDirect_zero_iff s).mpr h)

/-- 途中が零圏の元の二胞体の対角一単体は、同じ零値完全関手を表す。 -/
theorem stableTriangleDiagonal_zero (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌)
    (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩)) :
    StableArrowZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s) :=
  (stableTriangleDirect_zero_iff s).mp
    (stableTriangleLongHom_zero s hZ (ComposableArrows.mk₀ coherentTriangleDirectPath))

end SerrePositivity.KST.Fibration
