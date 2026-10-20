module
public import SerrePositivity.KST.SConstruction.OuterBinaryPasting

/-! # 元の両外側段三角形全体を同じ対角補正辺へ貼る
概要：既存の外側二部分面の全対角辺へ、元の左右段三角形全体を接続する。
方針：元の全対角辺の厳密な一致を使い、二回の pushout へ降ろす。
規約：元の全十面・両全正規化円柱を保持し、段面を充填し直さない。
使われ方：左右の共有直接補正と元の指定 BF 比較辺を同じ複体へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

/-- 元の左外側段面を同じ全対角辺へ貼った中間複体。 -/
def outerStageLeftDomain : SSet.{u} :=
  pushout (stdSimplex.δ.{u} (1 : Fin 3) ≫ outerBinaryPastingLeftCell.{u})
    (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の外側二部分面までの全複体の包含。 -/
def outerStageLeftOriginal : outerBinaryPasting.{u} ⟶ outerStageLeftDomain :=
  pushout.inl (stdSimplex.δ.{u} (1 : Fin 3) ≫ outerBinaryPastingLeftCell.{u})
    (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の左全段面の包含。 -/
def outerStageLeftCell : (Δ[2] : SSet.{u}) ⟶ outerStageLeftDomain :=
  pushout.inr (stdSimplex.δ.{u} (1 : Fin 3) ≫ outerBinaryPastingLeftCell.{u})
    (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の右全対角補正辺は、左段面の接続後も同じ全辺。 -/
def outerStageRightAttachingEdge : (Δ[1] : SSet.{u}) ⟶ outerStageLeftDomain :=
  stdSimplex.δ 1 ≫ outerBinaryPastingRightCell ≫ outerStageLeftOriginal

/-- 元の両外側全段面を接続した実複体。 -/
def outerStagePasting : SSet.{u} :=
  pushout outerStageRightAttachingEdge.{u} (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の全八面・両全円柱を持つ複体全体の包含。 -/
def outerStagePastingOriginal : outerBinaryPasting.{u} ⟶ outerStagePasting :=
  outerStageLeftOriginal ≫
    pushout.inl outerStageRightAttachingEdge.{u} (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の左外側全段面の同じ包含。 -/
def outerStagePastingLeftCell : (Δ[2] : SSet.{u}) ⟶ outerStagePasting :=
  outerStageLeftCell ≫
    pushout.inl outerStageRightAttachingEdge.{u} (stdSimplex.δ.{u} (1 : Fin 3))

/-- 元の右外側全段面の同じ包含。 -/
def outerStagePastingRightCell : (Δ[2] : SSet.{u}) ⟶ outerStagePasting :=
  pushout.inr outerStageRightAttachingEdge.{u} (stdSimplex.δ.{u} (1 : Fin 3))

variable {E : SSet.{u}} (P : outerBinaryPasting.{u} ⟶ E) (L R : (Δ[2] : SSet.{u}) ⟶ E)
  (hl : stdSimplex.δ 1 ≫ outerBinaryPastingLeftCell ≫ P = stdSimplex.δ 1 ≫ L)
  (hr : stdSimplex.δ 1 ≫ outerBinaryPastingRightCell ≫ P = stdSimplex.δ 1 ≫ R)

/-- 元の左全段面と既存複体全体を同時に保持する中間写像。 -/
def outerStageLeftMap : outerStageLeftDomain ⟶ E :=
  pushout.desc
    (f := stdSimplex.δ.{u} (1 : Fin 3) ≫ outerBinaryPastingLeftCell.{u})
    (g := stdSimplex.δ.{u} (1 : Fin 3)) P L ((Category.assoc _ _ _).trans hl)

/-- 中間写像は、元の既存複体全体を厳密に回収する。 -/
lemma outerStageLeftMap_original : outerStageLeftOriginal ≫ outerStageLeftMap P L hl = P :=
  pushout.inl_desc _ _ _

/-- 中間写像も、元の左全段三角形そのものを厳密に回収する。 -/
lemma outerStageLeftMap_cell : outerStageLeftCell ≫ outerStageLeftMap P L hl = L :=
  pushout.inr_desc _ _ _

/-- 元の両全段面と既存の全八面・両全円柱を同時に保持する実写像。 -/
def outerStagePastingMap : outerStagePasting ⟶ E :=
  pushout.desc (f := outerStageRightAttachingEdge.{u}) (g := stdSimplex.δ.{u} (1 : Fin 3))
    (outerStageLeftMap P L hl) R
    (by
      rw [outerStageRightAttachingEdge]
      simp only [Category.assoc]
      rw [outerStageLeftMap_original]
      exact hr)

/-- 元の全八面・両全正規化円柱の複体全体を厳密に回収する。 -/
lemma outerStagePastingMap_original :
    outerStagePastingOriginal ≫ outerStagePastingMap P L R hl hr = P := by
  rw [outerStagePastingOriginal, outerStagePastingMap, Category.assoc, pushout.inl_desc,
    outerStageLeftMap_original]

/-- 元の左外側全段面を厳密に回収する。 -/
lemma outerStagePastingMap_left :
    outerStagePastingLeftCell ≫ outerStagePastingMap P L R hl hr = L := by
  rw [outerStagePastingLeftCell, outerStagePastingMap, Category.assoc, pushout.inl_desc,
    outerStageLeftMap_cell]

/-- 元の右外側全段面も厳密に回収する。 -/
lemma outerStagePastingMap_right :
    outerStagePastingRightCell ≫ outerStagePastingMap P L R hl hr = R := pushout.inr_desc _ _ _

end SerrePositivity.KST.SConstruction
