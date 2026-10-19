module
public import SerrePositivity.KST.SConstruction.FamilyChainPasting

/-! # 元の三角形に全補正円柱列を貼る
概要：元の三角形の第二面に実補正列の入口を貼り、全セルと出口を保持する。
方針：補正列の実複体と元の三角形の間で一回の pushout を取る。
規約：元の三角形・全円柱・共有面を複体内で厳密に保持する。
使われ方：元の合成適合三角形と二次元補正を一つの実比較複体にする。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
variable {R E : SSet.{u}} (t : R ⊗ (Δ[2] : SSet.{u}) ⟶ E) {g : R ⊗ (Δ[1] : SSet.{u}) ⟶ E}
  (c : FamilyHomotopyChain ((R ◁ stdSimplex.δ 0) ≫ t) g)

/-- 元の三角形の第二面に、全円柱列の入口を貼った複体。 -/
def triangleCylinderPastingDomain : SSet.{u} :=
  pushout (R ◁ stdSimplex.δ 0) (familyChainPasting c).source

/-- 元の三角形全体の包含。 -/
def triangleCylinderPastingTriangle : R ⊗ (Δ[2] : SSet.{u}) ⟶ triangleCylinderPastingDomain t c :=
  pushout.inl (R ◁ stdSimplex.δ 0) (familyChainPasting c).source

/-- 元の全円柱列の複体全体の包含。 -/
def triangleCylinderPastingStrip :
    (familyChainPasting c).domain ⟶ triangleCylinderPastingDomain t c :=
  pushout.inr (R ◁ stdSimplex.δ 0) (familyChainPasting c).source

/-- 元の三角形と全円柱列を同時に保持する、複体全体の実写像。 -/
def triangleCylinderPastingMap : triangleCylinderPastingDomain t c ⟶ E :=
  pushout.desc (f := R ◁ stdSimplex.δ 0) (g := (familyChainPasting c).source)
    t (familyChainPasting c).map (familyChainPasting c).source_eq.symm

/-- 第二面と円柱列の入口は、貼り合わせ複体内で厳密に同じ全区間。 -/
lemma triangleCylinderPasting_shared :
    (R ◁ stdSimplex.δ 0) ≫ triangleCylinderPastingTriangle t c =
      (familyChainPasting c).source ≫ triangleCylinderPastingStrip t c :=
  pushout.condition

/-- 元の三角形全体を厳密に回収する。 -/
lemma triangleCylinderPastingMap_triangle :
    triangleCylinderPastingTriangle t c ≫ triangleCylinderPastingMap t c = t :=
  pushout.inl_desc _ _ _

/-- 元の全円柱複体の実写像を厳密に回収する。 -/
lemma triangleCylinderPastingMap_strip :
    triangleCylinderPastingStrip t c ≫ triangleCylinderPastingMap t c =
      (familyChainPasting c).map := pushout.inr_desc _ _ _

/-- 円柱列の出口も、元の終点円柱を全体として回収する。 -/
lemma triangleCylinderPastingMap_target :
    (familyChainPasting c).target ≫ triangleCylinderPastingStrip t c ≫
      triangleCylinderPastingMap t c = g := by
  rw [triangleCylinderPastingMap_strip]
  exact (familyChainPasting c).target_eq

/-- 貼り合わせ複体内の元の全円柱セル。 -/
def triangleCylinderPastingCells :=
  (familyChainPasting c).cells.map (· ≫ triangleCylinderPastingStrip t c)

/-- 元の全円柱セルと共有面・両端の厳密な歩道を保持する。 -/
def triangleCylinderPastingWalk : CylinderCellWalk
    ((familyChainPasting c).source ≫ triangleCylinderPastingStrip t c)
    ((familyChainPasting c).target ≫ triangleCylinderPastingStrip t c)
    (triangleCylinderPastingCells t c) :=
  cylinderCellWalkMap (familyChainPasting c).walk (triangleCylinderPastingStrip t c)

/-- 各セル全体を元の全 trace と同じ順序で厳密に回収する。 -/
lemma triangleCylinderPastingMap_cells :
    (triangleCylinderPastingCells t c).map (· ≫ triangleCylinderPastingMap t c) =
      familyHomotopyChainTrace c := by
  simp only [triangleCylinderPastingCells, List.map_map, Function.comp_def,
    Category.assoc, triangleCylinderPastingMap_strip]
  exact (familyChainPasting c).cells_eq

end SerrePositivity.KST.SConstruction
