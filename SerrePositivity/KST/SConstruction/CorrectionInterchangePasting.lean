module
public import SerrePositivity.KST.SConstruction.CorrectionPastingTriangleAttachment

/-! # 元の四面複体と両全交換三角形の同じ実貼り合わせ
概要：指定ホーンへ交換第二面を貼り、その共通対角に交換第一面を全体として貼る。
方針：元の二つの全三角形の全対角辺の一致を、二度目の pushout に渡す。
規約：元の全六面を保持し、Kan 充填や面の取り替えを使わない。
使われ方：三入力の左右の全補正辺路を、同じ六面実複体の境界として回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

/-- 元の四面複体に、同じ二つの全交換面を順に貼った実複体。 -/
def correctionInterchangePasting : SSet.{u} :=
  pushout (stdSimplex.δ.{u} (1 : Fin 3) ≫ correctionPastingTriangleCell.{u})
    (stdSimplex.δ.{u} (1 : Fin 3))

/-- 交換第二面までの元の実複体全体の包含。 -/
def correctionInterchangePastingIntermediate :
    correctionPastingTriangleDomain.{u} ⟶ correctionInterchangePasting :=
  pushout.inl (stdSimplex.δ.{u} (1 : Fin 3) ≫ correctionPastingTriangleCell.{u})
    (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の四面複体全体の同じ包含。 -/
def correctionInterchangePastingOriginal :
    doubleDiagonalTrianglePasting.{u} 0 2 ⟶ correctionInterchangePasting :=
  correctionPastingTriangleOriginal ≫ correctionInterchangePastingIntermediate

/-- 元の交換第二三角形全体の同じ包含。 -/
def correctionInterchangePastingSecond : (Δ[2] : SSet.{u}) ⟶ correctionInterchangePasting :=
  correctionPastingTriangleCell ≫ correctionInterchangePastingIntermediate

/-- 元の交換第一三角形全体の同じ包含。 -/
def correctionInterchangePastingFirst : (Δ[2] : SSet.{u}) ⟶ correctionInterchangePasting :=
  pushout.inr (stdSimplex.δ.{u} (1 : Fin 3) ≫ correctionPastingTriangleCell.{u})
    (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の両全交換面の共通対角は、同じ実複体内で厳密に同じ全区間。 -/
lemma correctionInterchangePasting_diagonal :
    stdSimplex.δ 1 ≫ correctionInterchangePastingSecond.{u} =
      stdSimplex.δ 1 ≫ correctionInterchangePastingFirst := by
  change _ ≫ correctionPastingTriangleCell ≫ correctionInterchangePastingIntermediate = _
  exact (Category.assoc _ _ _).symm.trans pushout.condition

variable {E : SSet.{u}} (P : doubleDiagonalTrianglePasting.{u} 0 2 ⟶ E)
  (T S : (Δ[2] : SSet.{u}) ⟶ E)
  (hl : correctionPastingLower ≫ P = stdSimplex.δ 2 ≫ T)
  (hu : correctionPastingUpper ≫ P = stdSimplex.δ 0 ≫ T)
  (hd : stdSimplex.δ 1 ≫ T = stdSimplex.δ 1 ≫ S)

/-- 元の全六面を同時に保持する、同じ実比較複体全体の写像。 -/
def correctionInterchangePastingMap : correctionInterchangePasting ⟶ E :=
  pushout.desc
    (f := stdSimplex.δ.{u} (1 : Fin 3) ≫ correctionPastingTriangleCell.{u})
    (g := stdSimplex.δ.{u} (1 : Fin 3)) (correctionPastingTriangleMap P T hl hu) S
    (by rw [Category.assoc, correctionPastingTriangleMap_cell]; exact hd)

/-- 元の四面複体全体を厳密に回収する。 -/
lemma correctionInterchangePastingMap_original :
    correctionInterchangePastingOriginal ≫ correctionInterchangePastingMap P T S hl hu hd = P := by
  rw [correctionInterchangePastingOriginal, correctionInterchangePastingMap,
    correctionInterchangePastingIntermediate,
    Category.assoc,
    pushout.inl_desc, correctionPastingTriangleMap_original]

/-- 元の全交換第二面を厳密に回収する。 -/
lemma correctionInterchangePastingMap_second :
    correctionInterchangePastingSecond ≫ correctionInterchangePastingMap P T S hl hu hd = T := by
  rw [correctionInterchangePastingSecond, correctionInterchangePastingMap,
    correctionInterchangePastingIntermediate,
    Category.assoc,
    pushout.inl_desc, correctionPastingTriangleMap_cell]

/-- 元の全交換第一面も厳密に回収する。 -/
lemma correctionInterchangePastingMap_first :
    correctionInterchangePastingFirst ≫ correctionInterchangePastingMap P T S hl hu hd = S :=
  pushout.inr_desc _ _ _

end SerrePositivity.KST.SConstruction
