module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.FiniteSpanNerveIso
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：有限 span の二つの実 nerve 辺を、標準ホーンの元の二辺へ照合する。
方針：全単体の符号写像と標準単体への包含の一致を評価する。
規約：両辺は半順序の元の射から構成し、同型の逆像として定義しない。
使われ方：span の全形状同型で両脚と端点を固定したことの公開確認。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 有限 span の始点から左終点への実 nerve 辺。 -/
def finiteSpanLeftEdge : (Δ[1] : SSet.{u}) ⟶ nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u} :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (homOfLE
    (show (ULift.up .zero : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u}) ≤ ULift.up .left from Or.inl rfl)))

/-- 有限 span の始点から右終点への実 nerve 辺。 -/
def finiteSpanRightEdge : (Δ[1] : SSet.{u}) ⟶ nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u} :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (homOfLE
    (show (ULift.up .zero : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u}) ≤ ULift.up .right from Or.inl rfl)))

/-- 左辺を元の 0→1 の標準辺へ厳密に戻す。 -/
lemma finiteSpanLeftEdge_iso : finiteSpanLeftEdge.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso.hom =
    horn₂₀.ι₀₁ := by
  apply (cancel_mono (horn 2 0).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso_hom_ι]
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 右辺を元の 0→2 の標準辺へ厳密に戻す。 -/
lemma finiteSpanRightEdge_iso : finiteSpanRightEdge.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso.hom =
    horn₂₀.ι₀₂ := by
  apply (cancel_mono (horn 2 0).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso_hom_ι]
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
