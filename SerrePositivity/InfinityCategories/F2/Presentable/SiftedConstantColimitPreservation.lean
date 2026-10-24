module

public import SerrePositivity.InfinityCategories.F2.Presentable.ContractibleConstantColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedContractibility
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedColimitPreservation
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift

/-!
概要：任意の指定頂点への定値関手は元の小さい sifted 余極限を保存する。
方針：添字の弱可縮性による一点への cofinality を宇宙持ち上げして用いる。
規約：元の全余錐の像を保持する。
使われ方：有限余積の変数を固定した関手族の保存条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の小さい弱可縮な形状の宇宙持ち上げから一点への射も right cofinal。
方針：元の一点射の cofinality を持ち上げ、一点の宇宙比較同型を合成する。
規約：元の形状に充填性を要求しない。
使われ方：大きい標的での小さい定値余極限。 -/
lemma pointProjection_ulift_isRightCofinal {K : SSet.{u}} (hK : IsWeaklyContractible K) :
    IsRightCofinal (stdSimplex.isTerminalObj₀.from ((SSet.uliftFunctor.{u + 1, u}).obj K)) := by
  have h := (Ind.isRightCofinal_ulift (stdSimplex.isTerminalObj₀.from K)
    (pointProjection_isRightCofinal hK)).comp
      (isRightCofinal_of_isIso (uliftStdSimplexIso.{u, u + 1} 0).hom)
  have he : (SSet.uliftFunctor.{u + 1, u}).map (stdSimplex.isTerminalObj₀.from K) ≫
      (uliftStdSimplexIso.{u, u + 1} 0).hom = stdSimplex.isTerminalObj₀.from _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ h

/-- 概要：定値関手は元の任意の小さい sifted 余極限を保存する。
方針：像の全余錐を元の全定値余錐へ厳密に照合する。
規約：標的の quasicategory 性だけを要求する。
使われ方：有限余積比較の各変数での生成表示。 -/
lemma constant_preservesSmallSiftedColimits {X Y : SSet.{u + 1}} [Quasicategory Y]
    (y : Y _⦋0⦌) : PreservesSmallSiftedColimits (SSet.const y : X ⟶ Y) := by
  intro I hI p c _
  have hc := constantJoinCocone_isColimit_of_pointCofinal
    (pointProjection_ulift_isRightCofinal (isWeaklyContractible_of_sifted I)) y
  have hv : (mapJoinCocone (SSet.const y) c).val =
      (constantJoinCocone ((SSet.uliftFunctor.{u + 1, u}).obj I) y).val := SSet.comp_const _ _
  exact (isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr hc

end SerrePositivity.InfinityCategories.F2.Presentable
