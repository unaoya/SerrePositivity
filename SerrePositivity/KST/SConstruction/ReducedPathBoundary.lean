module
public import SerrePositivity.KST.SConstruction.ReducedPathDiagonal
public import SerrePositivity.KST.SConstruction.IteratedPathBoundary

/-! # 定数経路を潰した境界射
概要：経路境界は定数経路上で元の零段の対角への包含となり、点つき商へ降りる。
方針：先頭を忘れる面と定数単体作用素の合成を計算する。
規約：標的は一つの零段を潰す reducedDiagonal。使われ方：点つき経路境界の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 概要：経路の境界は定数切断を元の零段の対角への包含に送る。
方針：後続頂点の包含の後で零段へ送る単体作用素は零段への唯一の射である。
規約：厳密等号。使われ方：点つき境界の商への降下条件。 -/
lemma simplicialPathDiagonalSection_boundary (X : SimplicialObject SSet.{u}) :
    simplicialPathDiagonalSection X ≫ simplicialPathDiagonalBoundary X = diagonalZeroColumn X := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  change (X.map (SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop)).op ≫
      X.map (simplicialPathTail d.unop).op).app d z =
    (X.map (SimplexCategory.const d.unop ⦋0⦌ 0).op).app d z
  rw [← X.map_comp, ← op_comp]
  have he : simplicialPathTail d.unop ≫
      SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop) =
        SimplexCategory.const d.unop ⦋0⦌ 0 := Subsingleton.elim _ _
  rw [he]

/-- 概要：定数経路を潰した点つき経路から、元の零段を潰した実現への境界射。
方針：境界は定数経路を標的の基点に送るので cofiber の普遍性で降ろす。
規約：全零方向の境界商との比較は別に行う。使われ方：点つき経路境界。 -/
def reducedPathDiagonalBoundary (X : SimplicialObject SSet.{u}) :
    reducedPathDiagonal X ⟶ reducedDiagonal X :=
  PointedObject.cofiberDesc (simplicialPathDiagonalSection X) (reducedDiagonal X)
    (simplicialPathDiagonalBoundary X ≫ diagonalReductionQuotient X) (by
      rw [← Category.assoc, simplicialPathDiagonalSection_boundary]
      exact PointedObject.cofiberQuotient_condition (diagonalZeroColumn X))

/-- 概要：点つき境界を商射影の前で引き戻すと元の経路境界と商写像の合成になる。
方針：cofiber の降下の式。
規約：厳密等号。使われ方：既存の境界射との比較。 -/
lemma reducedPathDiagonalBoundary_quotient (X : SimplicialObject SSet.{u}) :
    pathDiagonalReductionQuotient X ≫ (reducedPathDiagonalBoundary X).right =
      simplicialPathDiagonalBoundary X ≫ diagonalReductionQuotient X :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：定数経路を潰した点つき境界は単体的図式の写像について自然。
方針：商の元で経路境界の自然性と標的の商写像の自然性を使う。
規約：厳密な点つき射の等号。使われ方：反復境界の関手性。 -/
lemma reducedPathDiagonalBoundary_naturality {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    reducedPathDiagonalMap f ≫ reducedPathDiagonalBoundary Y =
      reducedPathDiagonalBoundary X ≫ reducedDiagonalMap f := by
  apply PointedObject.cofiber_hom_ext (simplicialPathDiagonalSection X)
  change pathDiagonalReductionQuotient X ≫
      ((reducedPathDiagonalMap f).right ≫ (reducedPathDiagonalBoundary Y).right) =
    pathDiagonalReductionQuotient X ≫
      ((reducedPathDiagonalBoundary X).right ≫ (reducedDiagonalMap f).right)
  rw [← Category.assoc, reducedPathDiagonalMap_quotient, Category.assoc,
    reducedPathDiagonalBoundary_quotient, ← Category.assoc]
  have he : simplicialDiagonalFunctor.map (Functor.whiskerLeft SimplexPrefix.functor.op f) ≫
      simplicialPathDiagonalBoundary Y = simplicialPathDiagonalBoundary X ≫
        simplicialDiagonalFunctor.map f := by
    exact (simplicialDiagonalFunctor.map_comp
      (Functor.whiskerLeft SimplexPrefix.functor.op f) (simplicialPathBoundary Y)).symm.trans
        ((congrArg simplicialDiagonalFunctor.map (simplicialPathBoundary_naturality f)).trans
          (simplicialDiagonalFunctor.map_comp (simplicialPathBoundary X) f))
  rw [he, Category.assoc, ← reducedDiagonalMap_quotient,
    ← Category.assoc, ← reducedPathDiagonalBoundary_quotient, Category.assoc]

/-- 概要：点つき経路境界を単体的図式上の自然変換にまとめる。
方針：構成した点つき境界と自然性を束ねる。
規約：源も標的も既存の cofiber による商。使われ方：反復への適用。 -/
def reducedPathDiagonalBoundaryNat : reducedPathDiagonalFunctor.{u} ⟶ reducedDiagonalFunctor where
  app := reducedPathDiagonalBoundary
  naturality {_X _Y} f := reducedPathDiagonalBoundary_naturality f

end SerrePositivity.KST.SConstruction
