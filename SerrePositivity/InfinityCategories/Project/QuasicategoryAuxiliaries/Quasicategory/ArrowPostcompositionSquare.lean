module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：二つの合成可能な辺を、始点の縦辺が厳密な恒等である実正方形へ拡張する。
方針：内二ホーンの充填を、正方形の頂点を 0,1,0,2 へ送る単調写像で引き戻す。
規約：元の第一辺と標的の辺を保持。使われ方：span の cocartesian lift の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

def arrowPostcompositionFoldOrder : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.1 = 0 then 0 else if p.2 = 0 then 1 else 2
  monotone' := by decide

def arrowPostcompositionFold : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFoldOrder

lemma arrowPostcompositionFold_zero : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

lemma arrowPostcompositionFold_target : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold = stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

lemma arrowPostcompositionFold_source : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold = stdSimplex.isTerminalObj₀.from Δ[1] ≫
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

lemma exists_arrowPostcompositionSquare {X : SSet.{u}} [Quasicategory X]
    {a b c : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) a b)
    (g : Truncated.Edge (X := (truncation 2).obj X) b c) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      SSet.ι₀ ≫ H = SSet.yonedaEquiv.symm f.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ H = SSet.const a ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ H = SSet.yonedaEquiv.symm g.edge := by
  obtain ⟨⟨k, t⟩⟩ := Truncated.Quasicategory₂.fill21 f g
  let T : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t.simplex
  have ht₂ : stdSimplex.δ (2 : Fin 3) ≫ T = SSet.yonedaEquiv.symm f.edge := by
    dsimp only [T]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm t.d₂
  have ht₀ : stdSimplex.δ (0 : Fin 3) ≫ T = SSet.yonedaEquiv.symm g.edge := by
    dsimp only [T]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm t.d₀
  have hf₀ : stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge = SSet.const a := by
    apply SSet.yonedaEquiv.injective
    change X.δ 1 f.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact f.src_eq
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold ≫ T, ?_, ?_, ?_⟩
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold_zero, ht₂]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold_source, Category.assoc, Category.assoc, ht₂]
    exact (congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ X =>
      stdSimplex.isTerminalObj₀.from Δ[1] ≫ k) hf₀).trans (SSet.comp_const _ _)
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold_target, ht₀]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPostcompositionFold := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFoldOrder (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPostcompositionFoldOrder := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFoldOrder

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPostcompositionFold_source := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPostcompositionFold_target := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPostcompositionFold_zero := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFold_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_arrowPostcompositionSquare := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.exists_arrowPostcompositionSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPostcompositionFoldOrder._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFoldOrder._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPostcompositionFoldOrder._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFoldOrder._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPostcompositionFoldOrder._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPostcompositionFoldOrder._proof_3
