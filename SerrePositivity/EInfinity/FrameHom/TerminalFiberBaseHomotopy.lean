module

public import SerrePositivity.InfinityCategories.Derived.RoofTerminalEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorTerminal
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing

/-!
# 終対象 fiber への実評価の全底ホモトピーと一意性

概要：元の実評価の円柱を底へ射影し、終対象に定値な全関手への唯一の射と比較する。
方針：同じ fiber 包含の底の式と全関手圏の点ごとの終対象性を使う。
規約：元の全円柱を保ち、パラメータ空間への条件は付けない。
使われ方：実屋根三角形の左脚と標準評価との全関手圏での同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {E B S : SSet.{u}} (p : E ⟶ B) (t : B _⦋0⦌)
  (R : RoofTerminalEvaluation p t) (g : S ⟶ E)

def terminalFiberBaseHomotopy : SSet.Homotopy (g ≫ p) (SSet.const (X := S) t) := by
  let H := functorHomotopyPostcomp (functorHomotopyPrecomp R.homotopy g) p
  apply stableHomotopyRetarget H
  · exact congrArg (fun f => f ≫ p) (Category.comp_id g)
  · simp only [Category.assoc, vertexFiberι_comp, SSet.comp_const]

lemma terminalFiberBaseHomotopy_h : (terminalFiberBaseHomotopy p t R g).h =
    (g ▷ (Δ[1] : SSet.{u})) ≫ R.homotopy.h ≫ p := rfl

lemma terminalFiberBaseHomotopy_hom_eq [Quasicategory B] (ht : IsTerminalVertex t)
    (H : SSet.Homotopy (g ≫ p) (SSet.const (X := S) t)) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (terminalFiberBaseHomotopy p t R g)) =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) := by
  have hconst : IsTerminalVertex (functorVertex (SSet.const (X := S) t)) :=
    isTerminalVertex_functorVertex_of_pointwise _ (fun _ => by
      change IsTerminalVertex (PinchedHom.constant t 0)
      rw [pinchedConstant_zero]
      exact ht)
  exact hconst.isTerminalHo.hom_ext _ _

lemma terminalFiberBaseHomotopy_hom_eq_retarget [Quasicategory B] (ht : IsTerminalVertex t)
    (d : S ⟶ B) (hd : g ≫ p = d) (H : SSet.Homotopy d (SSet.const (X := S) t)) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (stableHomotopyRetarget (terminalFiberBaseHomotopy p t R g) hd rfl)) =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) := by
  subst d
  exact terminalFiberBaseHomotopy_hom_eq p t R g ht H

end SerrePositivity.EInfinity.FrameHom
