module
public import SerrePositivity.KST.Fibration.VerdierLowerTriangleZeroHom
public import SerrePositivity.KST.Fibration.StableTriangleHomOverDiagonal

/-! # 指定 Verdier 上下二胞体の共有対角を保つ、同じ Hom 内の全零値関手族 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の指定 Verdier 四角形の二つの二胞体を、一つの有限添字で保持する。 -/
def verdierTriangle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌ :=
  d.square.app (Opposite.op ⦋2⦌) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j))

/-- 共有対角は、元の上側二胞体の同じ対角一単体。 -/
def verdierNullDiagonal (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌ :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 (verdierUpperTriangle d)

/-- 元の上下両方の対角面は、同じ共有対角と厳密に一致する。 -/
theorem verdierTriangle_diagonal (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 (verdierTriangle d j) = verdierNullDiagonal d := by
  fin_cases j
  · rfl
  · exact (verdierTriangle_sharedDiagonal d).symm

/-- 元の共有対角の実完全関手は、同じ零値関手である。 -/
theorem verdierNullDiagonal_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    StableArrowZeroVertex (verdierNullDiagonal d) :=
  stableTriangleDiagonal_zero _ (verdierUpperTriangle_middle_isZero d)

/-- 上下の元の二胞体を、共有対角の同じ両端を持つ全 Hom 内の族として読む。 -/
def verdierNullHomFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    nerve (CategoryTheory.SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
      ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩ ⟶[SSet.{u}]
        (verdierNullDiagonal d).obj ⟨ULift.up 1⟩) :=
  stableTriangleHomOverDiagonal (verdierNullDiagonal d) (verdierTriangle d j)
    (verdierTriangle_diagonal d j)

/-- 直接 path の像は、上下とも指定した共有対角の同じ実 Hom 頂点である。 -/
theorem verdierNullHomFamily_direct (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (verdierNullHomFamily d j).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleDirectPath) =
        coherentArrowHomVertex (verdierNullDiagonal d) :=
  stableTriangleHomOverDiagonal_direct _ _ _

/-- 共有対角の座標で読んだ元の両二胞体の全族は、全頂点で零値条件を満たす。 -/
theorem verdierNullHomFamily_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    ∀ v, StableHomZeroVertex ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
      ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)
      ((verdierNullHomFamily d j).app (Opposite.op ⦋0⦌) v) :=
  stableTriangleHomOverDiagonal_zero _ _ _ (verdierNullDiagonal_zero d)

/-- 上下二胞体の全長 Hom の同じ実族を比較する全関手同型。指定点相対性は別条件。 -/
def verdierNullHomFamilyIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierNullHomFamily d j) (verdierNullHomFamily d k) :=
  zeroStableHomFamilyIso _ _ (verdierNullHomFamily_zero d j) (verdierNullHomFamily_zero d k)

end SerrePositivity.KST.Fibration
