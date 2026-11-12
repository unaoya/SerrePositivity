module
public import SerrePositivity.KST.Fibration.StableTriangleDiagonalZero

/-! # 元の対角一単体の等号に沿い、二胞体の全長 Hom の対象座標だけを輸送する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 指定した対角一単体の両端を用い、元の二胞体の全長 Hom を読む同じ実射。 -/
def stableTriangleHomOverDiagonal (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s = a) :
    nerve (CategoryTheory.SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
      (a.obj ⟨ULift.up 0⟩ ⟶[SSet.{u}] a.obj ⟨ULift.up 1⟩) :=
  h ▸ (show _ ⟶ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s).obj ⟨ULift.up 0⟩ ⟶[SSet.{u}]
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s).obj ⟨ULift.up 1⟩) from coherentTriangleLongHom s)

/-- 座標輸送後の直接 path の値は、指定した同じ対角の実 Hom 頂点と厳密に一致。 -/
theorem stableTriangleHomOverDiagonal_direct (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s = a) :
    (stableTriangleHomOverDiagonal a s h).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleDirectPath) = coherentArrowHomVertex a := by
  subst a
  exact coherentTriangleDirect_vertex s

/-- 指定した対角の零値条件は、同じ全長 Hom の座標輸送後にも全頂点で保たれる。 -/
theorem stableTriangleHomOverDiagonal_zero (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s = a)
    (ha : StableArrowZeroVertex a) :
    ∀ v, StableHomZeroVertex (a.obj ⟨ULift.up 0⟩) (a.obj ⟨ULift.up 1⟩)
      ((stableTriangleHomOverDiagonal a s h).app (Opposite.op ⦋0⦌) v) := by
  subst a
  exact stableTriangleLongHom_zero_of_diagonal s ha

end SerrePositivity.KST.Fibration
