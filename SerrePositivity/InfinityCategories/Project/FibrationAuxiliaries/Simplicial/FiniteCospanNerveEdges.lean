module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FiniteCospanNerveIso

/-!
概要：有限 cospan の実 nerve 辺を、標準ホーンの元の二辺へ照合する。
方針：順序双対の両射に、span の反転で構成した全単体同型を作用させる。
規約：元の半順序の射から両辺を作り、終点の番号を反転規約に合わせる。
使われ方：cospan の極限存在の移送で両脚と端点を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 標準 0→2 に対応する、有限 cospan の実 nerve 辺。 -/
def finiteCospanLeftEdge : (Δ[1] : SSet.{u}) ⟶ nerve _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FiniteCospanIndex.{u} :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (homOfLE
    (show (OrderDual.toDual (ULift.up .right : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u})) ≤
      OrderDual.toDual (ULift.up .zero : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u}) from Or.inl rfl)))

/-- 標準 1→2 に対応する、有限 cospan の実 nerve 辺。 -/
def finiteCospanRightEdge : (Δ[1] : SSet.{u}) ⟶ nerve _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FiniteCospanIndex.{u} :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (homOfLE
    (show (OrderDual.toDual (ULift.up .left : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u})) ≤
      OrderDual.toDual (ULift.up .zero : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u}) from Or.inl rfl)))

/-- 左辺を元の 0→2 の標準辺へ厳密に戻す。 -/
lemma finiteCospanLeftEdge_iso : finiteCospanLeftEdge.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.finiteCospanNerveIso.hom =
    horn₂₂.ι₀₂ := by
  apply (cancel_mono (horn 2 2).ι).mp
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 右辺を元の 1→2 の標準辺へ厳密に戻す。 -/
lemma finiteCospanRightEdge_iso : finiteCospanRightEdge.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.finiteCospanNerveIso.hom =
    horn₂₂.ι₁₂ := by
  apply (cancel_mono (horn 2 2).ι).mp
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
