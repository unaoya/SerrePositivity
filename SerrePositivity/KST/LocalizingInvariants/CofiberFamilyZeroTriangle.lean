module

public import SerrePositivity.KST.LocalizingInvariants.DiagramFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.CofiberSquareFamily
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

/-- 零頂点の存在は、任意のパラメータの関手圏へ移る。 -/
lemma functorHasZeroVertex (A X : SSet.{u}) [Quasicategory X] [HasZeroVertex X] :
    HasZeroVertex ((ihom A).obj X) := by
  let z : A ⟶ X := SSet.const (chosenZeroVertex X).vertex
  have hz : ∀ a : A _⦋0⦌, IsZeroVertex (z.app (Opposite.op ⦋0⦌) a) := by
    intro a
    rw [show z = SSet.const (chosenZeroVertex X).vertex from rfl, zeroDiagram_const_vertex]
    exact (chosenZeroVertex X).isZero
  exact ⟨⟨functorVertex z, isInitialVertex_functorVertex_of_pointwise z (fun a => (hz a).1),
    isTerminalVertex_functorVertex_of_pointwise z (fun a => (hz a).2)⟩⟩

namespace CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

/-- 元の普遍四角形の左上の零角を与える全関手。 -/
def zeroCorner : A ⟶ X := squares X a ≫ evaluateFunctorAt
  (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma zeroCorner_zero (x : A _⦋0⦌) : IsZeroVertex ((zeroCorner X a).app (Opposite.op ⦋0⦌) x) := by
  have hs : functorVertex (squareAt X a x) = (squares X a).app (Opposite.op ⦋0⦌) x :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change IsZeroVertex ((evaluateFunctorAt _).app (Opposite.op ⦋0⦌) ((squares X a).app _ x))
  rw [← hs, evaluateFunctorAt_functorVertex]
  exact squareAt_zero X a x

/-- 元の全族を一つの関手圏内の零角四角形として保持する。 -/
def functorZeroTriangle : ZeroTriangle ((ihom A).obj X) where
  square := diagramFamilyTranspose (squares X a)
  zero_corner := by
    change IsZeroVertex ((diagramFamilyTranspose (squares X a)).app (Opposite.op ⦋0⦌) _)
    rw [diagramFamilyTranspose_vertex]
    exact ⟨isInitialVertex_functorVertex_of_pointwise (zeroCorner X a)
      (fun x => (zeroCorner_zero X a x).1),
      isTerminalVertex_functorVertex_of_pointwise (zeroCorner X a)
        (fun x => (zeroCorner_zero X a x).2)⟩

local instance cofiberFamilyFunctorZero : HasZeroVertex ((ihom A).obj X) :=
  functorHasZeroVertex A X

/-- cofiber 全族の下辺と右辺の合成は h Fun で零。 -/
lemma functorZeroTriangle_comp_zero :
    squareHoBottom (functorZeroTriangle X a).square ≫
      squareHoRight (functorZeroTriangle X a).square = 0 :=
  (functorZeroTriangle X a).homMk_comp_eq_zero

end CofiberFamily
end SerrePositivity.KST.LocalizingInvariants
