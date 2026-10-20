module
public import SerrePositivity.KST.SConstruction.CorrectionPastingHorn

/-! # 元の四面複体へ指定交換三角形全体を貼る
概要：元の四面複体の指定内ホーンに、元の同じ交換第二三角形全体を貼り合わせる。
方針：二つの全辺の厳密な一致からホーン写像の一致を証明し、pushout へ降ろす。
規約：三角形を充填し直さず、元の全四面複体と全交換三角形の像を保持する。
使われ方：六面補正比較複体の最初の交換面の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

/-- 元の内ホーンに指定全三角形を貼った実複体。 -/
def correctionPastingTriangleDomain : SSet.{u} :=
  pushout correctionPastingHorn.{u} (SSet.horn 2 (1 : Fin 3)).ι

/-- 元の全四面複体の同じ包含。 -/
def correctionPastingTriangleOriginal :
    doubleDiagonalTrianglePasting.{u} 0 2 ⟶ correctionPastingTriangleDomain :=
  pushout.inl correctionPastingHorn.{u} (SSet.horn 2 (1 : Fin 3)).ι

/-- 元の指定全交換三角形の同じ包含。 -/
def correctionPastingTriangleCell : (Δ[2] : SSet.{u}) ⟶ correctionPastingTriangleDomain :=
  pushout.inr correctionPastingHorn.{u} (SSet.horn 2 (1 : Fin 3)).ι

/-- 元の全内ホーンは、貼り合わせ複体内で指定三角形の同じ全ホーン。 -/
lemma correctionPastingTriangle_shared :
    correctionPastingHorn.{u} ≫ correctionPastingTriangleOriginal =
      (SSet.horn 2 (1 : Fin 3)).ι ≫ correctionPastingTriangleCell := pushout.condition

variable {E : SSet.{u}} (P : doubleDiagonalTrianglePasting.{u} 0 2 ⟶ E)
  (T : (Δ[2] : SSet.{u}) ⟶ E)
  (hl : correctionPastingLower ≫ P = stdSimplex.δ 2 ≫ T)
  (hu : correctionPastingUpper ≫ P = stdSimplex.δ 0 ≫ T)

include hl hu in
/-- 元の両全辺の一致は、同じ全ホーンの一致を与える。 -/
lemma correctionPastingHorn_map :
    correctionPastingHorn ≫ P = (SSet.horn 2 (1 : Fin 3)).ι ≫ T := by
  apply horn₂₁.isPushout.hom_ext
  · rw [← Category.assoc, correctionPastingHorn_lower, ← Category.assoc, SSet.horn.ι_ι]
    exact hl
  · rw [← Category.assoc, correctionPastingHorn_upper, ← Category.assoc, SSet.horn.ι_ι]
    exact hu

/-- 元の四面複体と指定全交換三角形を同時に保持する全実写像。 -/
def correctionPastingTriangleMap : correctionPastingTriangleDomain ⟶ E :=
  pushout.desc (f := correctionPastingHorn.{u}) (g := (SSet.horn 2 (1 : Fin 3)).ι)
    P T (correctionPastingHorn_map P T hl hu)

/-- 元の全四面複体を厳密に回収する。 -/
lemma correctionPastingTriangleMap_original :
    correctionPastingTriangleOriginal ≫ correctionPastingTriangleMap P T hl hu = P :=
  pushout.inl_desc _ _ _

/-- 元の指定全交換三角形も厳密に回収する。 -/
lemma correctionPastingTriangleMap_cell :
    correctionPastingTriangleCell ≫ correctionPastingTriangleMap P T hl hu = T :=
  pushout.inr_desc _ _ _

end SerrePositivity.KST.SConstruction
