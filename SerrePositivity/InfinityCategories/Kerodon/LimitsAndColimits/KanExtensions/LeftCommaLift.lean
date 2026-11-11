module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaHomotopy

/-!
概要：指定変換 δa→b から反転した comma への族を構成する。
方針：指定変換を反転して既存の comma に持ち上げ、パラメータの二重反転を戻す。
規約：quasicategory 性は不要。
使われ方：通常の局所 Kan 添字から cocartesian な置き換えの fiber への比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：指定変換 δa→b を反転した comma の向きへ移す。
方針：ホモトピーの反転の端点を合成の形に正規化する。
規約：射の合成は Mathlib の向き。
使われ方：comma の普遍性の入力。 -/
def kanLeftCommaLiftOppositeHomotopy {A K C : SSet.{u}} (δ : K ⟶ C)
    (a : A ⟶ K) (b : A ⟶ C) (H : SSet.Homotopy (a ≫ δ) b) :
    SSet.Homotopy (SSet.opFunctor.map b) (SSet.opFunctor.map a ≫ SSet.opFunctor.map δ) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H

/-- 概要：指定された両射影と変換から oriented fiber product への族を作る。
方針：反転した指定変換を comma へ持ち上げ、二重反転の逆同型を前合成する。
規約：高次の指定ホモトピーをそのまま保持する。
使われ方：局所添字上の標準余錐を fiber の図式へ比較する。 -/
def kanLeftCommaLift {A K C : SSet.{u}} (δ : K ⟶ C)
    (a : A ⟶ K) (b : A ⟶ C) (H : SSet.Homotopy (a ≫ δ) b) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftComma δ :=
  (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift (SSet.opFunctor.map δ) (SSet.opFunctor.map b) (SSet.opFunctor.map a)
      (kanLeftCommaLiftOppositeHomotopy δ a b H))

/-- 概要：指定変換の持ち上げは元の添字への射影を保つ。
方針：反転した comma の標的の式と二重反転の自然性を用いる。
規約：任意のパラメータ A。
使われ方：元の図式の制限の厳密な比較。 -/
lemma kanLeftCommaLift_source {A K C : SSet.{u}} (δ : K ⟶ C)
    (a : A ⟶ K) (b : A ⟶ C) (H : SSet.Homotopy (a ≫ δ) b) :
    kanLeftCommaLift δ a b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ = a := by
  change (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift (SSet.opFunctor.map δ) (SSet.opFunctor.map b) (SSet.opFunctor.map a)
      (kanLeftCommaLiftOppositeHomotopy δ a b H) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget (SSet.opFunctor.map δ)) ≫
          (SSet.opFunctorCompOpFunctorIso.app K).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_target]
  have hn := SSet.opFunctorCompOpFunctorIso.hom.naturality a
  change SSet.opFunctor.map (SSet.opFunctor.map a) ≫
    (SSet.opFunctorCompOpFunctorIso.app K).hom =
      (SSet.opFunctorCompOpFunctorIso.app A).hom ≫ a at hn
  rw [hn, Iso.inv_hom_id_assoc]

/-- 概要：指定変換の持ち上げは底への射影を保つ。
方針：反転した comma の始域の式と二重反転の自然性を用いる。
規約：射の厳密な等式。
使われ方：固定した頂点上の fiber への持ち上げ。 -/
lemma kanLeftCommaLift_projection {A K C : SSet.{u}} (δ : K ⟶ C)
    (a : A ⟶ K) (b : A ⟶ C) (H : SSet.Homotopy (a ≫ δ) b) :
    kanLeftCommaLift δ a b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ = b := by
  change (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift (SSet.opFunctor.map δ) (SSet.opFunctor.map b) (SSet.opFunctor.map a)
      (kanLeftCommaLiftOppositeHomotopy δ a b H) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (SSet.opFunctor.map δ)) ≫
          (SSet.opFunctorCompOpFunctorIso.app C).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_source]
  have hn := SSet.opFunctorCompOpFunctorIso.hom.naturality b
  change SSet.opFunctor.map (SSet.opFunctor.map b) ≫
    (SSet.opFunctorCompOpFunctorIso.app C).hom =
      (SSet.opFunctorCompOpFunctorIso.app A).hom ≫ b at hn
  rw [hn, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
