module

public import SerrePositivity.InfinityCategories.F1B.KanCocartesianInnerAnodynePullback
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomInnerFibration

/-!
概要：cocartesian fibration の相対指数の射影が inner fibration になることを示す。
方針：内ホーンの逆像の前合成同値を、実際の図式の厳密な延長へ移す。
規約：標的 D は quasicategory、底 C の充填性は射影の inner fibration 性には不要。
使われ方：Kerodon Lemma 5.3.6.6、Kan 拡張の族の全空間の充填性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cocartesian fibration の内ホーンの逆像の前合成同値により相対指数は inner fibration。
方針：Over 圏の生成内ホーンに平坦性を適用し、構成済みの延長判定へ渡す。
規約：底の quasicategory 性やモデル構造を要求しない。
使われ方：一般の kanFiberwiseHom の全空間の充填性。 -/
instance kanFiberwiseHomProjection_innerFibration {K C D : SSet.{u}}
    (p : K ⟶ C) [CocartesianFibration p] [Quasicategory D] :
    InnerFibration (kanFiberwiseHomProjection p D) := by
  apply kanFiberwiseHomProjection_innerFibration_of_hornEquivalences p
  intro n k h₀ hn b
  exact kanCocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence p
    (Over.homMk (horn (n + 2) k).ι rfl :
      Over.mk ((horn (n + 2) k).ι ≫ b) ⟶ Over.mk b)
    (innerHornInclusions.intro k h₀ hn)

/-- 概要：quasicategory 上の cocartesian fibration の相対指数の全空間は quasicategory。
方針：射影の inner fibration 性から全空間の内ホーンを充填する。
規約：fiber ごとの関手圏だけでなく実際の全空間について主張する。
使われ方：相対 Kan 拡張の族の写像空間を扱うための構造。 -/
instance kanFiberwiseHom_quasicategory {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p] :
    Quasicategory (kanFiberwiseHom p D) :=
  quasicategory_of_innerFibration (kanFiberwiseHomProjection p D)

end SerrePositivity.InfinityCategories
