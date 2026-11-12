module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContractibleConstantColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedContractibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SiftedColimitPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift

/-!
概要：任意の指定頂点への定値関手は元の小さい sifted 余極限を保存する。
方針：添字の弱可縮性による一点への cofinality を宇宙持ち上げして用いる。
規約：元の全余錐の像を保持する。
使われ方：有限余積の変数を固定した関手族の保存条件。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories


/-- 概要：元の小さい弱可縮な形状の宇宙持ち上げから一点への射も right cofinal。
方針：元の一点射の cofinality を持ち上げ、一点の宇宙比較同型を合成する。
規約：元の形状に充填性を要求しない。
使われ方：大きい標的での小さい定値余極限。 -/
lemma pointProjection_ulift_isRightCofinal {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (stdSimplex.isTerminalObj₀.from ((SSet.uliftFunctor.{u + 1, u}).obj K)) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift (stdSimplex.isTerminalObj₀.from K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointProjection_isRightCofinal hK)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0).hom)
  have he : (SSet.uliftFunctor.{u + 1, u}).map (stdSimplex.isTerminalObj₀.from K) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0).hom = stdSimplex.isTerminalObj₀.from _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ h

/-- 概要：定値関手は元の任意の小さい sifted 余極限を保存する。
方針：像の全余錐を元の全定値余錐へ厳密に照合する。
規約：標的の quasicategory 性だけを要求する。
使われ方：有限余積比較の各変数での生成表示。 -/
lemma constant_preservesSmallSiftedColimits {X Y : SSet.{u + 1}} [Quasicategory Y]
    (y : Y _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits (SSet.const y : X ⟶ Y) := by
  intro I hI p c _
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantJoinCocone_isColimit_of_pointCofinal
    (pointProjection_ulift_isRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.isWeaklyContractible_of_sifted I)) y
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (SSet.const y) c).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantJoinCocone ((SSet.uliftFunctor.{u + 1, u}).obj I) y).val := SSet.comp_const _ _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
