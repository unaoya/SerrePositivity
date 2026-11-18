module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：元の相対圏と同じ AsSmall 相対圏の hammock Hom を実同型で比較する。
方針：全語・全単体の各対象と射を up・down し、同じ全語図式の同型を余極限へ送る。
規約：元の両端点・全標準射・全作用素を保持する。
使われ方：宇宙調整前の実 frame 比較を balanced DK 模型へ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

/-- 概要：同じ AsSmall 圏の弱同値類。
方針：元の down に沿って逆像を取る。規約：元の射の弱同値。
使われ方：同じ hammock Hom の宇宙比較。 -/
abbrev weak : MorphismProperty (AsSmall.{max u v} C) := W.inverseImage AsSmall.down

/-- 概要：元の相対圏の同じ対象・射の持ち上げ。
方針：元の up と同じ弱同値性を束ねる。規約：元の全作用素。
使われ方：hammock 全図式の順射。 -/
def up : LocalizerMorphism W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) := ⟨AsSmall.up, fun _ _ _ h => h⟩

/-- 概要：同じ持ち上げた相対圏の元の対象・射への戻し。
方針：同じ down を使う。規約：元の弱同値を保持。
使われ方：hammock 全図式の逆射。 -/
def down : LocalizerMorphism (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) W := ⟨AsSmall.down, fun _ _ _ h => h⟩

variable (X Y : C)

/-- 概要：元の固定語の全 hammock 単体と同じ AsSmall 表示は実同型。
方針：全射列の同じ各成分を up・down する。
規約：元の語・全作用素。使われ方：全語図式の実同型。 -/
def graphIso (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) w (AsSmall.up.obj X) (AsSmall.up.obj Y) where
  hom := { app _ := ↾fun σ => σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.up W)
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun σ => σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.down W)
           naturality _ _ _ := rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    rfl

/-- 概要：同じ元の全語の hammock 図式は AsSmall 図式と実同型。
方針：同じ各語の実同型と元の相対関手の全語自然性を使う。
規約：全語の射を保持。使われ方：同じ余極限の比較。 -/
def diagramIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y) :=
  NatIso.ofComponents (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.graphIso W X Y) (by
    intro a b f
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    change σ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.up W)) =
      σ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.up W) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
    exact congrArg (fun H => σ ⋙ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_functor_eq (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.up W) f).symm)

/-- 概要：元の hammock Hom と AsSmall の同じ hammock Hom の実同型。
方針：元の全語図式の実同型を同じ余極限関手へ送る。
規約：元の全標準射を保持。使われ方：balanced DK 模型への frame 比較。 -/
def colimitIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y) :=
  colim.mapIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.diagramIso W X Y)

/-- 概要：同じ宇宙比較は元の各語の余極限標準射と可換。
方針：同じ余極限関手の自然性を読む。
規約：元の実標準射の等式。使われ方：元の frame roof の回収。 -/
lemma graphInclusion_colimitIso (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso W X Y).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.graphIso W X Y w).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y) w :=
  colimit.ι_map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.diagramIso W X Y).hom w

/-- 概要：元の AsSmall hammock 比較の順射自身は弱ホモトピー同値。
方針：同じ実同型を anodyne 局所化へ送る。
規約：単体集合モデルの仮定なし。使われ方：実 frame roof の弱比較の輸送。 -/
lemma colimitIso_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso W X Y).hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison
