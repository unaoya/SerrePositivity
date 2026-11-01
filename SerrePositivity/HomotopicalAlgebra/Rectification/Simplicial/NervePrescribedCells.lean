module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveLowerExtension
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.PrescribedLowerStep

/-!
# 中断した任意モデル源への一般化：NervePrescribedCells

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Retain independently specified cells with explicit face and degeneracy conditions。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0488][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0488
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Retain independently specified cells with explicit face and degeneracy conditions

Given a lower natural system, prescribe all cells of one new degree with
only their incoming direct and outgoing inverse compatibility. They form
one natural system and extend globally while preserving every selected
cell. This gives the same interface for edges, triangles and higher cells.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.NerveSimplexEndpoint
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NervePrescribedCells
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v}) (n : ℕ)
  (old : NerveLowerExtension.LowerSystem F n)

abbrev Data := PrescribedLowerStep.Data (NerveCoherentFamily.reedy D)
  (NerveCoherentFamily.simplices D) (NerveCoherentFamily.values F) n old

variable (cells : Data F n old)

/-- Assemble the selected new simplices before making any subsequent choices. -/
def assemble : NerveLowerExtension.LowerSystem F (n + 1) := cells.assemble

lemma assemble_old (s : Lower (NerveCoherentFamily.reedy D) n) :
    (assemble F n old cells).app ⟨s.obj, lt_trans s.property (Nat.lt_succ_self n)⟩ = old.app s :=
  cells.assemble_old s

lemma assemble_new (s : Index D) (hs : (NerveCoherentFamily.reedy D).deg s = n) :
    (assemble F n old cells).app ⟨s, hs ▸ Nat.lt_succ_self n⟩ = cells.hom s hs :=
  cells.assemble_new s hs

variable [ModelCategory SSet.{v}]
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

/-- One whole coherent extension retaining all independently supplied new cells. -/
def extend : NerveCoherentFamily.System F :=
  NerveLowerExtension.extend F hp hcof (n + 1) (assemble F n old cells)

lemma extend_old (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend F n old cells hp hcof).app s.obj = old.app s :=
  (NerveLowerExtension.extend_component F hp hcof (n + 1) (assemble F n old cells)
    ⟨s.obj, lt_trans s.property (Nat.lt_succ_self n)⟩).trans (assemble_old F n old cells s)

lemma extend_new (s : Index D) (hs : (NerveCoherentFamily.reedy D).deg s = n) :
    (extend F n old cells hp hcof).app s = cells.hom s hs :=
  (NerveLowerExtension.extend_component F hp hcof (n + 1) (assemble F n old cells)
    ⟨s, hs ▸ Nat.lt_succ_self n⟩).trans (assemble_new F n old cells s hs)

lemma extend_chain (c : ComposableArrows D n) :
    (extend F n old cells hp hcof).app (ofChain c) = cells.hom (ofChain c) rfl :=
  extend_new F n old cells hp hcof (ofChain c) rfl

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend F n old cells hp hcof) = old := by
  apply NatTrans.ext
  funext s
  exact extend_old F n old cells hp hcof s

end SerrePositivity.SimplicialModel.NervePrescribedCells
