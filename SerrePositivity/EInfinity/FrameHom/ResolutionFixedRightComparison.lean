module

public import SerrePositivity.EInfinity.FrameHom.ResolutionCofinality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.CostructuredArrowCofinality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.ArrowSpanComma
public import SerrePositivity.EInfinity.FrameHom.CofinalAnodyneImage

/-!
# 元の分解から各固定右脚への比較の余終性

概要：Low 命題 3.7 の中間 Hom の各固定終域で分解の余終性を証明する。
方針：同じ分解と左脚の slice の射影を AsSmall で揃えて元の comma の引き戻しへ渡す。
規約：元の分解と augmentation の全作用を保持し、単体集合モデルを要求しない。
使われ方：三本矢の右変数の全図式の成分ごとの比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.EInfinity.FrameHom

open CategoryTheory
open SerrePositivity.Reedy SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]

/-- 概要：左脚の slice の元の射影を同じ小さい宇宙へ送る（Low 命題 3.7）。
方針：元の左脚の始域の射影の前後で up・down を行う。
規約：元の対象と全可換三角形を保持する。
使われ方：固定右脚の costructured arrow の元の関手。 -/
def smallResolutionLeftForget (X : C) :
    AsSmall.{w} (TrivialFibrationOver X) ⥤ AsSmall.{w} C :=
  AsSmall.down ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (HomotopicalAlgebra.trivialFibrations C) X ⋙
    AsSmall.up

/-- 概要：左脚を忘れると元の同じ分解図式を厳密に回収（Low 命題 3.7）。
方針：元の augmentation の始域・全作用素と up/down の厳密な逆則を評価する。
規約：別の分解への置き換えを使わない。
使われ方：固定右脚の比較の始域と元の frame Hom の照合。 -/
lemma smallResolutionOverFunctor_leftForget {X : C}
    (q : CofibrantResolution (C := C) simplex X) :
    smallResolutionOverFunctor.{u, v, w} q ⋙ smallResolutionLeftForget X =
      AsSmall.down ⋙ q.obj ⋙ AsSmall.up := rfl

/-- 概要：固定した右対象に対する元の分解の比較（Low 命題 3.7）。
方針：元の分解の左脚の全可換三角形への比較を costructured arrow に適用する。
規約：同じ右対象の up と元の比較関手を使う。
使われ方：右脚の全図式の成分ごとの射。 -/
def resolutionFixedRightComparison {X : C} (q : CofibrantResolution (C := C) simplex X)
    (V : C) :
    CostructuredArrow (smallResolutionOverFunctor.{u, v, w} q ⋙ smallResolutionLeftForget X)
        (AsSmall.up.obj V) ⥤
      CostructuredArrow (smallResolutionLeftForget X) (AsSmall.up.obj V) :=
  CostructuredArrow.pre (smallResolutionOverFunctor q) (smallResolutionLeftForget X)
    (AsSmall.up.obj V)

/-- 概要：元の分解の比較は各固定右対象で left cofinal（Low 命題 3.7）。
方針：元の分解の余終性を costructured arrow の right fibration に沿って引き戻す。
規約：元の右対象の fibrancy は要求しない。
使われ方：全三本矢の右変数の図式の成分ごとの余終性。 -/
lemma resolutionFixedRightComparison_isLeftCofinal {X : C}
    (q : CofibrantResolution (C := C) simplex X) (V : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap (resolutionFixedRightComparison.{u, v, w} q V)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.costructuredArrowPre_isLeftCofinal _ _ _ (smallResolutionOverFunctor_isLeftCofinal q)

/-- 概要：各固定右対象で元の同じ比較は弱ホモトピー同値（Low 命題 3.7）。
方針：同じ比較射の left cofinality を全 Kan 標的による検査へ渡す。
規約：元の nerve の両端に Kan 性を要求しない。
使われ方：全図式の元の成分ごとのホモトピー型の比較。 -/
lemma resolutionFixedRightComparison_isWeakHomotopyEquivalence {X : C}
    (q : CofibrantResolution (C := C) simplex X) (V : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (resolutionFixedRightComparison.{u, v, w} q V)) :=
  (resolutionFixedRightComparison_isLeftCofinal q V).isWeakHomotopyEquivalence

/-- 概要：各固定右対象の元の比較は同じ anodyne 局所化で可逆（Low 命題 3.7）。
方針：元の比較の余終性を left anodyne・trivial Kan 因子分解で反転する。
規約：元の比較射と元の分解を保持する。
使われ方：三本矢の右変数の全図式の成分ごとの反転性。 -/
lemma resolutionFixedRightComparison_localized_isIso {X : C}
    (q : CofibrantResolution (C := C) simplex X) (V : C) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap (resolutionFixedRightComparison.{u, v, w} q V))) :=
  leftCofinal_localized_isIso _ (resolutionFixedRightComparison_isLeftCofinal q V)

end SerrePositivity.EInfinity.FrameHom
