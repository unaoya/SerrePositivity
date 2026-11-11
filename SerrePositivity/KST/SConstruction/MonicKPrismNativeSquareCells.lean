module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeCylinderTransport
public import SerrePositivity.KST.SConstruction.FamilySquareClockSwap

/-! # 二次元補正の全セルは元の同じ交換正方形
概要：保存済み二次元補正列と元の交換正方形列の全セルを厳密に照合する。
方針：元の二時刻を交換するだけの同じ実写像と、共通パラメータの制限を使う。
規約：全セル・全単体・順序を保存し、零面だけで代用しない。
使われ方：三角形に貼った全補正セルの四面の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の二次元補正全列は、元の交換正方形列の二時刻を交換した同じ全セル。 -/
lemma monicKPrismCompositeSecondCompatibilityTransport_square_cells (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismCompositeSecondCompatibilityTransport F f g n) =
      (monicKPrismCompatibilityInterchangeSquares F f g n).map
        (familySquareClockSwap
          (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ≫ ·) := by
  simp only [monicKPrismCompositeSecondCompatibilityTransport,
    monicKPrismCompositeCompatibilityTransportChain, familyHomotopyChainTargetTransport_trace,
    familyHomotopyChainSourceTransport_trace, familyInterchangeCylinderChain_trace_clockSwap,
    monicKPrismCompatibilityInterchangeSquares, pointedCompatibilityInterchangeSquares]
  rfl

/-- 共通三精密化上でも、貼る全セルは元の同じ交換正方形の全体である。 -/
lemma monicKPrismNativeSecondCompatibilityTransport_square_cells (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeSecondCompatibilityTransport F f g n) =
      (monicKPrismCompatibilityInterchangeSquares F f g n).map (fun q =>
        ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
          familySquareClockSwap
            (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ≫ q) := by
  rw [monicKPrismNativeSecondCompatibilityTransport_trace,
    monicKPrismCompositeSecondCompatibilityTransport_square_cells]
  simp only [List.map_map, Function.comp_def]

end SerrePositivity.KST.SConstruction
