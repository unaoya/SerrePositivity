module

public import SerrePositivity.KST.Spectra.ConstantHomotopyEndEvaluation

/-!
概要：定値 homotopy end の標準比較射は写像空間で定数族となる。
方針：strict な錐の weighted nerve の評価を最後の係数で計算する。
規約：基点の射にも適用できるよう任意のパラメーターからの射を許す。
使われ方：Goerss–Jardine VIII §2。自明作用の標準射と基点の保持。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (C : Type u) [SmallCategory C] {A X : SSet.{u}}

/-- 概要：任意の射から定値図式への定数の脚の錐を作る。
方針：すべての脚を同じ射とし、恒等射との可換性を使う。
規約：錐の頂点は A、定値係数は X。
使われ方：Goerss–Jardine VIII §2。標準比較と基点の統一した入力。 -/
def constantDiagramCone (f : A ⟶ X) : Cone ((Functor.const C).obj X) where
  pt := A
  π := { app _ := f, naturality _ _ _ := by simp }

lemma constantCone_nerveEvaluation (f : A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform
      (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight C) ((Functor.const C).obj A) ≫
        (constantDiagramCone C f).π) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantEvaluation C X =
      snd (nerve C) A ≫ f := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change ComposableArrows C n × A _⦋n⦌ at s
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients
    (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight C) ((Functor.const C).obj A) ≫
      (constantDiagramCone C f).π) s.1 (SSet.yonedaEquiv.symm s.2)).app (Fin.last n)) =
        f.app _ s.2
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveCoefficients_cone_app (constantDiagramCone C f), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  change SSet.yonedaEquiv (SSet.yonedaEquiv.symm s.2 ≫ f) = f.app _ s.2
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 概要：定値図式の標準 end 比較は nerve の変数に一定な族である。
方針：写像空間同型の普遍評価と、錐の最後の係数の評価を照合する。
規約：f が基点なら同じ式が点つき比較の基点条件を与える。
使われ方：Goerss–Jardine VIII §2。自明作用の Shapiro の実際の標準射の照合。 -/
lemma constantHomotopyEndIso_cone (f : A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (constantDiagramCone C f) ≫
        (constantHomotopyEndIso C X).hom = curry (snd (nerve C) A ≫ f) := by
  apply uncurry_injective
  rw [uncurry_natural_left, constantHomotopyEndIso_uncurry, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_weightedNerveEvaluation, constantCone_nerveEvaluation,
    uncurry_curry]
  rfl

end

end SerrePositivity.KST.Spectra
