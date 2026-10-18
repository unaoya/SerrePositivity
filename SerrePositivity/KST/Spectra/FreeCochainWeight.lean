module

public import SerrePositivity.KST.Spectra.GroupActionCochains
public import Mathlib.CategoryTheory.Action.Monoidal

/-!
概要：群作用の cochain の各次数の重みを自由 G 集合の重みに同定する。
方針：EG_n の G^(n+1) を左正則 G 集合と自明 G^n との積に分解する。
規約：同型は実際の作用図式と点つき end の同型として与える。
使われ方：Goerss–Jardine VIII §2。cochain 各値の Kan 性と標準群 cochain との比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet Opposite

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：EG の次数 n の重みは G × G^n の自由作用の離散重みと同型。
方針：群の斉次座標から非斉次座標への既存の作用の同型を送る。
規約：G は第一因子だけに左正則作用し、第二因子への作用は自明。
使われ方：Goerss–Jardine VIII §2。各次数の自由軌道による cochain の表示。 -/
def universalCoverFreeIso (G : Type u) [Group G] (n : ℕ) :
    (universalCoverWeight G).obj (op (SimplexCategory.mk n)) ≅
      (actionWeightFunctor G).obj (Action.leftRegular G ⊗ Action.trivial G (Fin n → G)) :=
  (actionWeightFunctor G).mapIso (Action.diagonalSuccIsoTensorTrivial G n)

/-- 概要：群作用の cochain の各次数は自由作用の重みの同変内部 Hom と同型。
方針：重みの作用図式の同型を end の反変関手で送る。
規約：Kan 性はこの同型だけからはまだ主張しない。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain 各値の関数空間の表示への比較。 -/
def cochainFreeIso {G : Type u} [Group G] (A : GroupAction.{u} G) (k n : ℕ) :
    (level A k).obj (SimplexCategory.mk n) ≅
      PointedWeightedEnd.obj
        ((actionWeightFunctor G).obj
          (Action.leftRegular G ⊗ Action.trivial G (Fin n → G)))
        (AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A ⋙ OmegaSpectrum.levelEvaluation k) :=
  (PointedWeightedEnd.weightFunctor
    (AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A ⋙ OmegaSpectrum.levelEvaluation k)).mapIso
      (universalCoverFreeIso G n).symm.op

end

end SerrePositivity.KST.Spectra.GroupActionCochains
