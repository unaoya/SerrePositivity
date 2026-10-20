module
public import SerrePositivity.KST.SConstruction.TriangleDiagonalPasting

/-! # 元の二つの対角三角形複体を共有全辺で貼る
概要：各々が二つの全三角形を保持する実複体を、指定した同じ全辺で貼り合わせる。
方針：二つの元の第二三角形の指定面包含を使って、もう一つの pushout を取る。
規約：四つの全二単体を同時に保持し、元の比較面を充填し直さない。
使われ方：前後二射の補正比較の四つの全三角形を、共通中間補正辺で一体化する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
variable (i j : Fin 3)

/-- 元の二つの二三角形複体を、第二三角形の指定全辺で貼った複体。 -/
def doubleDiagonalTrianglePasting : SSet.{u} :=
  pushout (stdSimplex.δ.{u} i ≫ triangleDiagonalPastingSecond.{u})
    (stdSimplex.δ.{u} j ≫ triangleDiagonalPastingSecond.{u})

/-- 第一の元の二三角形複体全体の包含。 -/
def doubleDiagonalTrianglePastingFirst :
    triangleDiagonalPasting.{u} ⟶ doubleDiagonalTrianglePasting i j :=
  pushout.inl (stdSimplex.δ.{u} i ≫ triangleDiagonalPastingSecond.{u})
    (stdSimplex.δ.{u} j ≫ triangleDiagonalPastingSecond.{u})

/-- 第二の元の二三角形複体全体の包含。 -/
def doubleDiagonalTrianglePastingSecond :
    triangleDiagonalPasting.{u} ⟶ doubleDiagonalTrianglePasting i j :=
  pushout.inr (stdSimplex.δ.{u} i ≫ triangleDiagonalPastingSecond.{u})
    (stdSimplex.δ.{u} j ≫ triangleDiagonalPastingSecond.{u})

/-- 元の共有全辺は、貼り合わせ複体内で厳密に同じ全区間。 -/
lemma doubleDiagonalTrianglePasting_shared :
    (stdSimplex.δ.{u} i ≫ triangleDiagonalPastingSecond.{u}) ≫
        doubleDiagonalTrianglePastingFirst i j =
      (stdSimplex.δ.{u} j ≫ triangleDiagonalPastingSecond.{u}) ≫
        doubleDiagonalTrianglePastingSecond i j := pushout.condition

variable {E : SSet.{u}} (P Q : triangleDiagonalPasting.{u} ⟶ E)
  (h : (stdSimplex.δ.{u} i ≫ triangleDiagonalPastingSecond.{u}) ≫ P =
    (stdSimplex.δ.{u} j ≫ triangleDiagonalPastingSecond.{u}) ≫ Q)

/-- 元の四つの全二単体を同時に保持する、貼り合わせ全体の実写像。 -/
def doubleDiagonalTrianglePastingMap : doubleDiagonalTrianglePasting i j ⟶ E :=
  pushout.desc (f := stdSimplex.δ.{u} i ≫ triangleDiagonalPastingSecond.{u})
    (g := stdSimplex.δ.{u} j ≫ triangleDiagonalPastingSecond.{u}) P Q h

/-- 第一の元の二三角形複体全体を厳密に回収する。 -/
lemma doubleDiagonalTrianglePastingMap_first :
    doubleDiagonalTrianglePastingFirst i j ≫ doubleDiagonalTrianglePastingMap i j P Q h = P :=
  pushout.inl_desc _ _ _

/-- 第二の元の二三角形複体全体も厳密に回収する。 -/
lemma doubleDiagonalTrianglePastingMap_second :
    doubleDiagonalTrianglePastingSecond i j ≫ doubleDiagonalTrianglePastingMap i j P Q h = Q :=
  pushout.inr_desc _ _ _

end SerrePositivity.KST.SConstruction
