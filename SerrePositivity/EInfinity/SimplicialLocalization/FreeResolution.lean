module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeResolutionDegrees
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution

/-!
# Dwyer–Kan の自由相対圏の全単体的解像

概要：Dwyer–Kan の自由相対圏 comonad を通常の単体圏上の解像へ代入する。
方針：既存の汎用 comonad 解像の六つの関係式と単体圏表示同値を使う。
規約：全単体作用素は実際の相対関手で、各次数の指定矢を保つ。
使われ方：各次数の普通の局所化から単体的局所化を構成する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory Opposite
open SerrePositivity.HomotopyFunctionComplex

/-- 概要：汎用 comonad の冪は同じ反復自由相対関手の値（Dwyer–Kan）。
方針：元の二つの反復の再帰式を次数に沿って照合する。
規約：元の相対圏と自由関手を保持する。
使われ方：全単体的解像の各次数の同定。 -/
lemma freeComonadPower_eq (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : ℕ) :
    ComonadResolutionOperators.power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freePower n).obj C := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeFunctor.obj ih

/-- 概要：通常の単体圏上の自由相対圏の全単体的解像（Dwyer–Kan）。
方針：同じ自由相対圏 comonad を全関係式のある汎用構成へ代入する。
規約：全作用素は指定する矢を保つ相対関手。
使われ方：単体的局所化の次数ごとの圏の図式。 -/
def freeResolution (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} :=
  ComonadSimplicialResolution.diagram _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C

/-- 概要：自由解像の各値は既存の同じ反復自由相対圏（Dwyer–Kan）。
方針：汎用解像の対象の式と冪の同定を合成する。
規約：通常の n 単体で評価する。
使われ方：各次数の自由な射の列の取り扱い。 -/
lemma freeResolution_obj (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : ℕ) :
    (freeResolution C).obj (op (SimplexCategory.mk n)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeResolutionLevel n).obj C :=
  freeComonadPower_eq C (n + 1)

/-- 概要：自由解像の各面は同じ comonad の面作用素（Dwyer–Kan）。
方針：汎用単体的解像の面の式を使う。
規約：全次数・全ての面を含む。
使われ方：自由圏の次数ごとの局所化との比較。 -/
lemma freeResolution_face (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {n : ℕ} (i : Fin (n + 2)) :
    (freeResolution C).δ i = ComonadResolutionOperators.face _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1) i :=
  ComonadSimplicialResolution.diagram_face _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C i

/-- 概要：自由解像の各退化は同じ comonad の退化作用素（Dwyer–Kan）。
方針：汎用単体的解像の退化の式を使う。
規約：全次数・全ての退化を含む。
使われ方：単体的局所化の退化作用素の照合。 -/
lemma freeResolution_degeneracy (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {n : ℕ} (i : Fin (n + 1)) :
    (freeResolution C).σ i = ComonadResolutionOperators.degeneracy _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n i :=
  ComonadSimplicialResolution.diagram_degeneracy _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C i

/-- 概要：全自由単体的解像から元の相対圏への自然な augmentation（Dwyer–Kan）。
方針：同じ comonad の汎用 augmentation を代入する。
規約：全単体作用素に自然。
使われ方：元の代数射と自由単体的局所化との比較。 -/
def freeResolutionAugmentationNatTrans (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    freeResolution C ⟶ (Functor.const SimplexCategoryᵒᵖ).obj C :=
  ComonadSimplicialResolution.augmentation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C

/-- 概要：全自由解像の augmentation は同じ冪の逐次合成（Dwyer–Kan）。
方針：元の汎用 augmentation の各次数の式を使う。
規約：元の comonad の余単位を使う。
使われ方：全作用素との自然性の成分の照合。 -/
lemma freeResolutionAugmentationNatTrans_app (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : ℕ) :
    (freeResolutionAugmentationNatTrans C).app (op (SimplexCategory.mk n)) =
      ComonadResolutionOperators.augmentation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1) := rfl

end SerrePositivity.EInfinity.SimplicialLocalization
