module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraRelativeInput
public import SerrePositivity.EInfinity.BarrattEccles.DiscreteAlgebra

/-!
# 離散可換代数から cofibrant E 代数の DK 入力への関手

概要：BF §1・Dwyer–Kan の構成に元の離散 E 代数を関手的に供給する。
方針：元の離散 E 代数関手と同じ cofibrant 置換を合成する。
規約：底の離散複体への自然な擬同型を保持する。∞ 圏の離散性は後続で証明する。
使われ方：E2b の離散対象の構成。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory _root_.HomotopicalAlgebra

variable (A : Type u) [CommRing A]

/-- 概要：通常の可換代数から cofibrant E 代数への関手（BF §1）。
方針：元の augmentation に沿う離散代数化と同じ置換を合成する。
規約：全代数射に関手的で元の環の標数に条件を付けない。
使われ方：CAlg_R の離散対象の具体的な cofibrant 模型。 -/
def discreteCofibrantAlgebraFunctor : CommAlgCat.{u} A ⥤ CofibrantAlgebra A :=
  discreteAlgebraFunctor A ⋙ cofibrantAlgebraReplacement A

/-- 概要：cofibrant 離散模型から元の離散 E 代数への比較（BF §1）。
方針：元の離散関手へ同じ置換比較を前合成する。
規約：元の離散代数関手の全射に自然。
使われ方：離散対象の元の複体との比較。 -/
def discreteCofibrantAlgebraComparison :
    discreteCofibrantAlgebraFunctor A ⋙ cofibrantAlgebraInclusion A ⟶ discreteAlgebraFunctor A :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (discreteAlgebraFunctor A) (cofibrantAlgebraReplacementComparison A) ≫
      (Functor.rightUnitor (discreteAlgebraFunctor A)).hom

/-- 概要：離散模型の比較は元の置換比較そのもの（Hovey §1.2）。
方針：関手の結合・単位比較の恒等成分を相殺する。
規約：新しい比較射を選ばない。
使われ方：底の擬同型性を元の分解から回収する。 -/
lemma discreteCofibrantAlgebraComparison_app (B : CommAlgCat.{u} A) :
    (discreteCofibrantAlgebraComparison A).app B =
      framedLimitProbeComparison A ((discreteAlgebraFunctor A).obj B) := by
  change 𝟙 _ ≫ framedLimitProbeComparison A ((discreteAlgebraFunctor A).obj B) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- 概要：cofibrant 離散模型から元の離散 E 代数への比較は弱同値（BF §1）。
方針：同じ元の置換比較の擬同型性を使う。
規約：cofibrant 置換後の底を元の零次複体へ擬同型で比較する。
使われ方：離散対象の同じホモトピー型の保持。 -/
lemma discreteCofibrantAlgebraComparison_weakEquivalence (B : CommAlgCat.{u} A) :
    let := modelCategory A
    weakEquivalences (operad A).Algebra ((discreteCofibrantAlgebraComparison A).app B) := by
  let := modelCategory A
  rw [discreteCofibrantAlgebraComparison_app]
  exact framedLimitProbeComparison_quasiIso A _

/-- 概要：通常の可換代数を同じ DK 入力の相対圏へ送る関手（Dwyer–Kan）。
方針：元の離散代数化と同じ Hom の宇宙を揃えた置換を合成する。
規約：対象と代数射は同じ元の関手的置換。
使われ方：CAlg_R の離散対象の単体的局所化への入力。 -/
def discreteAlgebraDKFunctor :
    CommAlgCat.{u} A ⥤ (cofibrantAlgebraRelativeCategory A).category :=
  discreteAlgebraFunctor A ⋙ cofibrantAlgebraDKReplacement A

end SerrePositivity.EInfinity.BarrattEccles
