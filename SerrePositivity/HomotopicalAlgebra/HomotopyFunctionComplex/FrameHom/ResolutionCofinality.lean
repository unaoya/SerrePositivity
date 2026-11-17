module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ResolutionAsphericity
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallCommaContraction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveQuillenA
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalWeakEquivalence

/-!
# 同じ分解の自明 fibration の slice への nerve の余終性

概要：Low 命題 3.6 の元の分解図式に F1b の Quillen A を適用する。
方針：全 comma の可縮性を同じ AsSmall の関手へ移し、native な slice を検査する。
規約：元の分解・augmentation・全作用素を保持し、単体集合モデルを要求しない。
使われ方：特殊な三本矢への共通比較の右射の分解側の余終性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom

open _root_.CategoryTheory
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.SimplicialModel
open _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [_root_.HomotopicalAlgebra.ModelCategory C] {X : C}

/-- 概要：元の分解図式の対象と Hom の宇宙を同時に揃える（Low 命題 3.6）。
方針：同じ resolutionOverFunctor の前後に元の down・up を置く。
規約：全作用素を同じ単体圏の持ち上げで保持する。
使われ方：F1b の同じ宇宙の小圏の判定の具体的な関手。 -/
def smallResolutionOverFunctor (q : CofibrantResolution (C := C) simplex X) :
    AsSmall.{max w u v} SimplexCategory ⥤ AsSmall.{w} (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.TrivialFibrationOver X) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma.smallFunctor.{0, 0, max u v, v, w} (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionOverFunctor q)

/-- 概要：元の分解図式の nerve は left cofinal（Low 命題 3.6、Quillen A）。
方針：全自明 fibration を終点とする元の comma の可縮性を同じ宇宙で検査する。
規約：終点や元の対象の cofibrancy を追加仮定しない。
使われ方：三本矢への右射の分解側のホモトピー余終性。 -/
lemma smallResolutionOverFunctor_isLeftCofinal
    (q : CofibrantResolution (C := C) simplex X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.smallResolutionOverFunctor.{u, v, w} q)) := by
  apply _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveQuillenA.nerveMap_isLeftCofinal
  intro t
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.AsSmallComma.terminal_localized_isIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionOverFunctor q)
    (AsSmall.down.obj t) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionCommaTerminal_image_isIso q (AsSmall.down.obj t)
      AnodyneHomotopy.anodyneQ (Localization.inverts _ SSet.anodyneExtensions))

/-- 概要：元の分解図式の nerve は弱ホモトピー同値（Low 命題 3.6）。
方針：元の left cofinality を全 Kan 標的の検査へ渡す。
規約：nerve の始域・終域の Kan 性は要求しない。
使われ方：分解側の同じ nerve の比較のホモトピー型。 -/
lemma smallResolutionOverFunctor_isWeakHomotopyEquivalence
    (q : CofibrantResolution (C := C) simplex X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.smallResolutionOverFunctor.{u, v, w} q)) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.smallResolutionOverFunctor_isLeftCofinal q).isWeakHomotopyEquivalence

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
