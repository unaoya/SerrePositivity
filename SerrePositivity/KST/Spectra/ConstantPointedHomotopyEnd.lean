module

public import SerrePositivity.KST.Spectra.ConstantHomotopyEndCone
public import SerrePositivity.KST.Spectra.PointedWeightedEndBasepoint

/-!
概要：定値点つき図式の homotopy end を基点を保つ写像空間で表示する。
方針：通常の内部 Hom に定数基点を選び、標準錐の比較式を使う。
規約：源の nerve には基点を固定しない。写像空間の基点だけを定数写像とする。
使われ方：Goerss–Jardine VIII §2。自明作用の hG の高次 π_* の計算。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet


namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace UnbasedPointedMapping

/-- 概要：任意の源から点つき係数への写像空間に定数基点を選ぶ。
方針：通常の内部 Hom を使い、係数の基点への定数族を curry する。
規約：源の点を固定する条件は課さない。
使われ方：Goerss–Jardine VIII §2。自明群作用の写像空間模型。 -/
def obj (K : SSet.{u}) (X : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  Under.mk (curry (snd K (𝟙_ SSet.{u}) ≫ X.hom))

instance kanComplex (K : SSet.{u}) (X : PointedSimplicialSet.{u}) [KanComplex X.right] :
    KanComplex (obj K X).right := by
  change KanComplex ((ihom K).obj X.right)
  infer_instance

end UnbasedPointedMapping

/-- 概要：定値点つき homotopy end の nerve からの写像空間への基点を保つ同型。
方針：基礎 end の忘却同型と定値図式の比較を合成し、基点の錐の式を適用する。
規約：C と係数の Kan 性に依存しない厳密な同型。
使われ方：Goerss–Jardine VIII §2。自明作用の homotopy fixed points の点つき表示。 -/
def constantPointedHomotopyEndIso (C : Type u) [SmallCategory C]
    (X : PointedSimplicialSet.{u}) :
    PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight C) ((Functor.const C).obj X) ≅
      UnbasedPointedMapping.obj (nerve C) X :=
  Under.isoMk
    (PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight C) ((Functor.const C).obj X) ≪≫
      constantHomotopyEndIso C X.right)
    (by
      rw [Iso.trans_hom, ← Category.assoc, PointedWeightedEnd.underlyingIso_basepoint]
      exact constantHomotopyEndIso_cone C X.hom)

end

end SerrePositivity.KST.Spectra
