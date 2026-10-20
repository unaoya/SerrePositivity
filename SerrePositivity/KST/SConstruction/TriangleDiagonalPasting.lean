module
public import SerrePositivity.KST.SConstruction.TriangleCylinderPasting

/-! # 元の二つの全三角形を同じ全対角辺で貼る
概要：元の二つの全二単体を、厳密に一致する対角辺で一つの実比較複体へ貼り合わせる。
方針：二つの標準三角形の対角包含の pushout を使い、元の両全写像を降ろす。
規約：Kan 充填や三角形の取り替えを使わず、両全二単体を厳密に保持する。
使われ方：元の段三角形と全二部分三角形を同じ補正辺路の二つの面として貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial

/-- 元の二つの全三角形を、それぞれの同じ対角辺で貼った実複体。 -/
def triangleDiagonalPasting : SSet.{u} :=
  pushout (stdSimplex.δ.{u} (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の第一全三角形の同じ包含。 -/
def triangleDiagonalPastingFirst : (Δ[2] : SSet.{u}) ⟶ triangleDiagonalPasting :=
  pushout.inl (stdSimplex.δ.{u} (1 : Fin 3)) (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の第二全三角形の同じ包含。 -/
def triangleDiagonalPastingSecond : (Δ[2] : SSet.{u}) ⟶ triangleDiagonalPasting :=
  pushout.inr (stdSimplex.δ.{u} (1 : Fin 3)) (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の全対角辺は、実貼り合わせ複体内で厳密に同じ全区間。 -/
lemma triangleDiagonalPasting_shared :
    stdSimplex.δ.{u} 1 ≫ triangleDiagonalPastingFirst.{u} =
      stdSimplex.δ.{u} 1 ≫ triangleDiagonalPastingSecond.{u} := pushout.condition

variable {E : SSet.{u}} (T U : (Δ[2] : SSet.{u}) ⟶ E)
  (h : stdSimplex.δ.{u} 1 ≫ T = stdSimplex.δ.{u} 1 ≫ U)

/-- 元の両全二単体を同時に保持する、実複体全体の同じ写像。 -/
def triangleDiagonalPastingMap : triangleDiagonalPasting ⟶ E :=
  pushout.desc (f := stdSimplex.δ.{u} (1 : Fin 3)) (g := stdSimplex.δ.{u} (1 : Fin 3)) T U h

/-- 元の第一全二単体を厳密に回収する。 -/
lemma triangleDiagonalPastingMap_first :
    triangleDiagonalPastingFirst ≫ triangleDiagonalPastingMap T U h = T :=
  pushout.inl_desc _ _ _

/-- 元の第二全二単体も厳密に回収する。 -/
lemma triangleDiagonalPastingMap_second :
    triangleDiagonalPastingSecond ≫ triangleDiagonalPastingMap T U h = U :=
  pushout.inr_desc _ _ _

/-- 第一全三角形の元の各全境界も、同じ実複体から厳密に回収する。 -/
lemma triangleDiagonalPastingMap_first_face (i : Fin 3) :
    stdSimplex.δ.{u} i ≫ triangleDiagonalPastingFirst ≫ triangleDiagonalPastingMap T U h =
      stdSimplex.δ.{u} i ≫ T := by
  rw [triangleDiagonalPastingMap_first]

/-- 第二全三角形の元の各全境界も、同じ実複体から厳密に回収する。 -/
lemma triangleDiagonalPastingMap_second_face (i : Fin 3) :
    stdSimplex.δ.{u} i ≫ triangleDiagonalPastingSecond ≫ triangleDiagonalPastingMap T U h =
      stdSimplex.δ.{u} i ≫ U := by
  rw [triangleDiagonalPastingMap_second]

end SerrePositivity.KST.SConstruction
