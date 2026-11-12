module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanDiagramExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.RepresentableComparison

/-!
概要：中央が Kan、両脚が fibration の cospan の実際の標準比較の同値性。
方針：中央成分を先に延長して左右の相対持ち上げを解き、重みの変更の一般の証明に渡す。
規約：このファイルの比較は両脚の fibration 性を要求する。一脚だけの場合は後続。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の isofibrant な引き戻し図式。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inr))]

/-- 概要：両脚が fibration の Kan cospan の任意の重み付き end は Kan 複体。
方針：ホーンを自然変換に移し、実装した cospan の成分ごとの anodyne な延長を使う。
規約：重み W に Kan 性や可縮性は要求しない。
使われ方：Kerodon 7.5.3（Tag 03AP） の切断空間の Kan 性。 -/
lemma weightedSections_cospan_kanComplex (W : AsSmall.{u} WalkingCospan ⥤ SSet.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_kanComplex_of_extensions W H
    (fun j hj a => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_resized_cospan_extension_of_anodyne j hj a)

/-- 概要：両脚が fibration の Kan cospan の end の成分ごとの anodyne な制限は trivial Kan fibration。
方針：境界と重みの相対直積に cospan の延長を適用する。
規約：二つの重みは任意の同じ宇宙の図式。
使われ方：Kerodon 7.5.3（Tag 03AP） の標準比較の補助重みの変更。 -/
lemma weightedSectionsPre_cospan_trivialKanFibration
    {W W' : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_trivialKanFibration_of_extensions j hj
    (fun j hj a => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_resized_cospan_extension_of_anodyne j hj a)

/-- 概要：両脚が fibration の Kan cospan の任意の極限錐からの標準比較はホモトピー同値。
方針：成分ごとの anodyne な延長を補助重みを用いる比較の定理へ渡す。
規約：c.pt の Kan 性は前提に追加しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の引き戻しの homotopy 極限錐。 -/
lemma bousfieldKanConeComparison_cospan_homotopyEquivalence (c : Cone H) (hc : IsLimit c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_homotopyEquivalence_of_extensions c hc
    (fun j hj a => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_resized_cospan_extension_of_anodyne j hj a)

/-- 概要：両脚が fibration の Kan cospan の実際の κ は単体的ホモトピー同値。
方針：任意の極限錐の比較を選択された極限錐に適用する。
規約：一脚だけの fibration 性での主張ではない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の isofibrant な引き戻し図式。 -/
lemma bousfieldKanLimitComparison_cospan_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H) :=
  bousfieldKanConeComparison_cospan_homotopyEquivalence H (limit.cone H) (limit.isLimit H)

/-- 概要：豊穣極限の Hom 図式が isofibrant な cospan なら実際の表現可能な q_x は同値。
方針：sHom で作った極限錐へ cospan の比較を適用する。
規約：Hom 図式の極限性と両脚の Fibration 性を明示する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の引き戻しでの検出の入力。 -/
lemma representableHomotopyLimitComparison_cospan_homotopyEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x))
    [KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).obj (AsSmall.up.obj .one))]
    [Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))]
    [Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inr))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) :=
  bousfieldKanConeComparison_cospan_homotopyEquivalence _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x) hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
