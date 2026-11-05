module
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamilyZeroTriangle

public import SerrePositivity.KST.LocalizingInvariants.DiagramFamilyTranspose
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberSquareFamily
public import SerrePositivity.InfinityCategories.Core.SquareHomotopyCategory

/-!
概要：元の cofiber 四角形の全族は関手圏内の零角四角形である。
方針：全族の転置と頂点評価の比較で零角を同定し、h Fun の合成の零性を得る。
規約：点ごとの零合成ではない。使われ方：差の実随伴単位の四辺の可換性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

namespace CofiberFamily
attribute [local instance] SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiberFamilyFunctorZero
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

/-- 元の全族を一つの関手圏内の零角四角形として保持する。 -/
def functorZeroTriangle : ZeroTriangle ((ihom A).obj X) where
  square := diagramFamilyTranspose (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a)
  zero_corner := by
    change IsZeroVertex ((diagramFamilyTranspose (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a)).app (Opposite.op ⦋0⦌) _)
    rw [diagramFamilyTranspose_vertex]
    exact ⟨isInitialVertex_functorVertex_of_pointwise (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroCorner X a)
      (fun x => (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroCorner_zero X a x).1),
      isTerminalVertex_functorVertex_of_pointwise (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroCorner X a)
        (fun x => (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroCorner_zero X a x).2)⟩

/-- cofiber 全族の下辺と右辺の合成は h Fun で零。 -/
lemma functorZeroTriangle_comp_zero :
    squareHoBottom (functorZeroTriangle X a).square ≫
      squareHoRight (functorZeroTriangle X a).square = 0 :=
  (functorZeroTriangle X a).homMk_comp_eq_zero

end CofiberFamily
end SerrePositivity.KST.LocalizingInvariants
