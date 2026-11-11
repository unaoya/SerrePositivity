module
public import SerrePositivity.KST.SConstruction.StableZeroSquareDiagonal
public import SerrePositivity.KST.SConstruction.StableZeroArrowHomotopies

/-!
概要：零角を持つ元四角形の上下全比較は共有対角で同じ射の類を持つ。
方針：元共有対角の零完全射回収と同じ両端経路の比較一意性を使う。
規約：元両二胞体・全比較を保持。使われ方：同じ類を保つ対角代表修正の入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 概要：元零四角形の上下二胞体全比較は同じ共有対角の全射の類を持つ。
方針：元対角完全射の全零性・二比較の可逆性・同じ両端経路を使う。
規約：元四角形と元二比較を保持。使われ方：元全比較の類を保つ共有対角整列。 -/
lemma squareFrameTriangleDiagonalHomotopy_homMk_eq_of_zero
    {f g : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}}
    (H : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare g))
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex f 0 1))) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (squareFrameTriangleDiagonalHomotopy H 0)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (squareFrameTriangleDiagonalHomotopy H 1)) :=
  stableZeroSourceHomotopy_homMk_eq _ _ (stableSquareDiagonalMap f)
    (stableSquareDiagonalMap_zero f hz) (stableSquareDiagonalMap_diagram f)
    (squareFrameTriangleDiagonalHomotopy H 0) (squareFrameTriangleDiagonalHomotopy H 1)
    (squareFrameTriangleDiagonalHomotopy_isInvertible H 0)
    (squareFrameTriangleDiagonalHomotopy_isInvertible H 1)
    (squareFrameTriangleDiagonalHomotopy_endpoints H).1
    (squareFrameTriangleDiagonalHomotopy_endpoints H).2
end SerrePositivity.KST.SConstruction
