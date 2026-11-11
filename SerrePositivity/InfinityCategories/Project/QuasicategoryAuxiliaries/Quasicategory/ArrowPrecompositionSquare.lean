module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowPostcompositionSquare

/-!
概要：合成可能な二辺を、終点の縦辺が恒等である実正方形にする。
方針：合成二単体を正方形の頂点 0,2,1,2 による単調写像で引き戻す。
規約：最終の横辺と始点の縦辺を保持し、元の合成二単体も返す。
使われ方：普遍 pullback による span の第一脚の前合成。
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
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

def arrowPrecompositionFoldOrder : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.1 = 1 then 2 else if p.2 = 0 then 0 else 1
  monotone' := by decide

def arrowPrecompositionFold : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFoldOrder

lemma arrowPrecompositionFold_one : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold = stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

lemma arrowPrecompositionFold_zero : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold = stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

lemma arrowPrecompositionFold_source : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

lemma arrowPrecompositionFold_target : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold = SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) := by
  apply SSet.yonedaEquiv.injective
  decide

lemma exists_arrowPrecompositionSquare {X : SSet.{u}} [Quasicategory X]
    {a b c : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) a b)
    (g : Truncated.Edge (X := (truncation 2).obj X) b c) :
    ∃ T : (Δ[2] : SSet.{u}) ⟶ X,
      stdSimplex.δ (2 : Fin 3) ≫ T = SSet.yonedaEquiv.symm f.edge ∧
      stdSimplex.δ (0 : Fin 3) ≫ T = SSet.yonedaEquiv.symm g.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold ≫ T = SSet.const c := by
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
  have hc : T.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) = c := by
    have hg₁ : (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm g.edge) = SSet.const c := by
      apply SSet.yonedaEquiv.injective
      change X.δ 0 g.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant c 0
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      exact g.tgt_eq
    have h := congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ X =>
      k.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
      (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ X => stdSimplex.δ (0 : Fin 2) ≫ k) ht₀ |>.trans hg₁)
    simp only [NatTrans.comp_app_apply] at h
    have hd : (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app (Opposite.op ⦋0⦌)
        ((stdSimplex.δ (0 : Fin 2)).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) =
            stdSimplex.obj₀Equiv.symm (2 : Fin 3) := by decide
    rw [hd] at h
    change T.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant c 0 at h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at h
    exact h
  refine ⟨T, ht₂, ht₀, ?_⟩
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_target, SSet.const_comp]
  exact congrArg SSet.const hc

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPrecompositionFold := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFoldOrder (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPrecompositionFoldOrder := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFoldOrder

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPrecompositionFold_one := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPrecompositionFold_source := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPrecompositionFold_target := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPrecompositionFold_zero := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_arrowPrecompositionSquare := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.exists_arrowPrecompositionSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPrecompositionFoldOrder._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFoldOrder._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPrecompositionFoldOrder._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFoldOrder._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowPrecompositionFoldOrder._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFoldOrder._proof_3
