module
public import SerrePositivity.KST.LocalizingInvariants.FinalHornContraction

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ArrowContractionSquares

/-!
概要：最終外ホーンの矢印族を正方形族へ移し、末尾二点を元の最後の辺と恒等辺へ同定する。
方針：ホーン内収縮の端点・辺の式を、三因子の正方形族へ移す。
規約：辺の代表と底辺の元の族を保持。使われ方：pullback の相対延長への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def finalHornArrowSquares {X : SSet.{u}} (m : ℕ)
    (σ : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.arrowContractionSquares (finalHornLastContraction m) σ

lemma finalHornArrowSquares_bottom {X : SSet.{u}} (m : ℕ)
    (σ : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    finalHornArrowSquares m σ ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app X = σ := by
  rw [finalHornArrowSquares, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.arrowContractionSquares_bottom,
    finalHornLastContraction_zero, Category.id_comp]

lemma finalHornArrowSquares_top {X : SSet.{u}} (m : ℕ)
    (σ : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    finalHornArrowSquares m σ ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge).app X =
      SSet.const (σ.app (Opposite.op ⦋0⦌) (finalHornLastVertex m)) := by
  rw [finalHornArrowSquares, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.arrowContractionSquares_top, finalHornLastContraction_one,
    SSet.const_comp]

lemma finalHornArrowSquares_right {X : SSet.{u}} (m : ℕ)
    (σ : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (β : (Δ[m + 2] : SSet.{u}) ⟶ X)
    (hβ : σ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ β) :
    finalHornArrowSquares m σ ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app X =
      curry ((Δ[1] ◁ (horn (m + 2) (Fin.last (m + 2))).ι) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (m + 2) ≫ β) := by
  rw [finalHornArrowSquares, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.arrowContractionSquares_right, hβ, ← Category.assoc,
    finalHornLastContraction_inclusion, Category.assoc]

lemma finalHorn_contractionAtVertex_penultimate (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.contractionAtVertex (finalHornLastContraction.{u} m) (finalHornPenultimateVertex m) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.contractionAtVertex, SSet.yonedaEquiv_comp]
  exact finalHornLastContraction_penultimate_edge m

lemma finalHorn_contractionAtVertex_last (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.contractionAtVertex (finalHornLastContraction.{u} m) (finalHornLastVertex m) =
      SSet.const (finalHornLastVertex m) := by
  apply SSet.yonedaEquiv.injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.contractionAtVertex, SSet.yonedaEquiv_comp]
  exact finalHornLastContraction_last_edge m

lemma finalHornArrowSquares_penultimate {X : SSet.{u}} (m : ℕ)
    (σ : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    (finalHornArrowSquares m σ).app (Opposite.op ⦋0⦌) (finalHornPenultimateVertex m) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (uncurry (SSet.yonedaEquiv.symm
        (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m)))) := by
  rw [finalHornArrowSquares, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.arrowContractionSquares_vertex,
    finalHorn_contractionAtVertex_penultimate, SSet.yonedaEquiv_symm_comp]

lemma finalHornArrowSquares_last {X : SSet.{u}} (m : ℕ)
    (σ : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    (finalHornArrowSquares m σ).app (Opposite.op ⦋0⦌) (finalHornLastVertex m) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (uncurry (SSet.const (σ.app (Opposite.op ⦋0⦌) (finalHornLastVertex m)) :
        (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X)) := by
  rw [finalHornArrowSquares, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.arrowContractionSquares_vertex,
    finalHorn_contractionAtVertex_last, SSet.const_comp]

end SerrePositivity.KST.LocalizingInvariants
