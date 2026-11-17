module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.NerveULiftHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne

/-!
# 宇宙を揃えた反対要素圏の nerve の元の Hom への反転可能な射

概要：共通比較の実際の始域から元の単体集合の同じ宇宙持ち上げへの比較を構成する。
方針：元の射列の Hom の ULift の実同型と同じ終端 augmentation を合成する。
規約：元の単体・全作用素・augmentation を保持する。
使われ方：Dwyer–Kan §7 の同じ Map^h への共通比較の左射。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v w

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve

open _root_.CategoryTheory
open _root_.SerrePositivity.SimplicialModel

/-- 概要：Hom の宇宙を上げた反対要素圏の nerve の同じ augmentation（Dwyer–Kan §7）。
方針：元の射列を down する実同型の後に同じ終端単体の制限を適用する。
規約：元の Hom の持ち上げだけを比較先に使う。
使われ方：実際の Map^h の共通比較の左射。 -/
def liftedAugmentation (K : SSet.{v}) :
    nerve (ULiftHom.{w} K.Elementsᵒᵖ) ⟶ SSet.uliftFunctor.{w, v}.obj K :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveULiftHom.iso K.Elementsᵒᵖ).hom ≫ SSet.uliftFunctor.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K)

/-- 概要：宇宙を上げた同じ augmentation は大きい宇宙で anodyne 反転後に可逆（Dwyer–Kan）。
方針：元の実同型と同じ小さい augmentation の反転性の宇宙持ち上げを合成する。
規約：単体集合のどの宇宙にもモデル構造を要求しない。
使われ方：実際の高次比較の左射の反転性。 -/
lemma liftedAugmentation_localized_isIso (K : SSet.{v}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation.{v, w} K)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (SSet.uliftFunctor.{w, v}.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K))) :=
    UniverseLift.anodyneQ_map_isIso_of_small _ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation_localized_isIso K)
  unfold _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation
  rw [Functor.map_comp]
  infer_instance

/-- 概要：持ち上げた終端 augmentation は同じ元の零単体を回収する（Dwyer–Kan §7）。
方針：射列の down と元の零次の正規化を合成する。
規約：元の零単体の ULift そのもの。
使われ方：実際の Map^h の共通比較の元の射での正規化。 -/
lemma liftedAugmentation_zero (K : SSet.{v}) (x : K.obj (Opposite.op (SimplexCategory.mk 0))) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation.{v, w} K).app (Opposite.op (SimplexCategory.mk 0))
        (ComposableArrows.mk₀ (show ULiftHom.{w} K.Elementsᵒᵖ from
          Opposite.op (K.elementsMk (Opposite.op (SimplexCategory.mk 0)) x))) = ULift.up x := by
  change ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalAugmentation.augmentation K).app
    (Opposite.op (SimplexCategory.mk 0))
      (ComposableArrows.mk₀ (Opposite.op (K.elementsMk
        (Opposite.op (SimplexCategory.mk 0)) x)))) = ULift.up x
  exact congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalAugmentation.augmentation_zero K x)

/-- 概要：持ち上げた同じ終端 augmentation も全係数射に自然（Dwyer–Kan §7）。
方針：元の nerve の宇宙比較と元の augmentation の同じ自然性を合成する。
規約：全作用素と同じ係数写像を保持する。
使われ方：共通比較の大きい宇宙での関手性。 -/
lemma liftedAugmentation_naturality {K M : SSet.{v}} (f : K ⟶ M) :
    nerveMap (ULiftHom.down.{0, v, w} ⋙ f.mapElements.op ⋙ ULiftHom.up) ≫
        _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation M = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation K ≫ SSet.uliftFunctor.map f := by
  unfold _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveULiftHom.naturality, Category.assoc,
    ← SSet.uliftFunctor.map_comp]
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveULiftHom.iso K.Elementsᵒᵖ).hom ≫ SSet.uliftFunctor.map
      (nerveMap f.mapElements.op ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalAugmentation.augmentation M) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalAugmentation.naturality, SSet.uliftFunctor.map_comp, Category.assoc]
  rfl

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve
