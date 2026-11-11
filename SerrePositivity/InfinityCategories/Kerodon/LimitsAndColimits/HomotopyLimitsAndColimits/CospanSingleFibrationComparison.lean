module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.InitialNerveCorner
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanOverRight
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanSingleFibrationPointComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.RepresentableComparison

/-!
概要：中央と右端が Kan、左脚だけが fibration の cospan の実際の標準比較の同値性。
方針：元の重みの右遷移の anodyne 性を相対錐の境界へ移し、補助重みの二つの制限を使う。
規約：右脚の fibration 性も未証明の相対境界の条件も要求しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の引き戻しの比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：元の Bousfield–Kan 重みから補助重みへの包含の中央の相対境界は anodyne。
方針：右遷移の over 圏の nerve の anodyne 性を、始対象の付加の相対境界へ移す。
規約：AsSmall に持ち上げた cospan の実際の重みを使う。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の一脚だけが fibration の標準比較の第二段階。 -/
lemma bousfieldKanConeWeightInclusion_cospan_corner_anodyne :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.cospanRightCornerMap (Functor.whiskerLeft AsSmall.up
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion (I := AsSmall.{u} WalkingCospan)))) := by
  have : (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_functor
  let r := (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).map
    WalkingCospan.Hom.inr
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight_map_mono r
  have : Mono (nerveMap (Over.map r)) := hm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.initialNerveCorner_anodyne (Over.map r)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight_cospan_inr_anodyne

variable (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]

/-- 概要：補助重みから元の重みへの実際の制限は一脚の fibration 性で trivial Kan fibration。
方針：成分ごとの anodyne 性と実際に検証した中央の相対境界を使う。
規約：中央と右端の Kan 性および左脚の Fibration 性を要求する。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の元の重み側の制限の同値性。 -/
lemma bousfieldKanConeWeightInclusion_cospan_leftFibration_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_cospan_leftFibration_trivialKanFibration
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion_anodyne
    bousfieldKanConeWeightInclusion_cospan_corner_anodyne

/-- 概要：補助重みから元の重みへの実際の制限は一脚の fibration 性でホモトピー同値。
方針：両重みの右脚の単射性と、相対境界から得た制限の同値性を使う。
規約：右脚の fibration 性は要求しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の κ の分解の第二の射。 -/
lemma bousfieldKanConeWeightInclusion_cospan_leftFibration_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion H) := by
  have : (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_functor
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight_map_mono (AsSmall.up.map WalkingCospan.Hom.inr)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeight_map_mono (AsSmall.up.map WalkingCospan.Hom.inr)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_cospan_leftFibration_homotopyEquivalence
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion_anodyne
    bousfieldKanConeWeightInclusion_cospan_corner_anodyne

/-- 概要：一脚が fibration の Kan cospan の任意の極限錐からの実際の標準比較は同値。
方針：strict 極限から補助 end への同値と、元の重みへの制限の同値を合成する。
規約：極限頂点の Kan 性は追加せず、中央と右端の Kan 性から導く。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の引き戻しの homotopy 極限の比較。 -/
lemma bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
    (c : Cone H) (hc : IsLimit c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) := by
  let U := (Functor.const (AsSmall.{u} WalkingCospan)).obj (Δ[0] : SSet.{u})
  have hU : IsTerminal U := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightIsTerminalOfObj U (fun _ => stdSimplex.isTerminalObj₀)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_isIso_of_isTerminalWeight U hU c hc
  have : Mono (U.map (AsSmall.up.map WalkingCospan.Hom.inr)) :=
    inferInstanceAs (Mono (𝟙 (Δ[0] : SSet.{u})))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_cospan_leftFibration_kanComplex U H
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison U c)).symm
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeight_cospan_leftFibration_kanComplex H
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_cospan_leftFibration_kanComplex H
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_factorization c]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightComparison_cospan_leftFibration_homotopyEquivalence H c hc).comp
    (bousfieldKanConeWeightInclusion_cospan_leftFibration_homotopyEquivalence H)

/-- 概要：一脚だけが fibration の cospan の選択された strict 極限からの実際の κ は同値。
方針：任意の極限錐の比較を選択された極限錐へ適用する。
規約：中央と右端が Kan、左脚が Fibration。右脚の条件は追加しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の引き戻しの比較。 -/
lemma bousfieldKanLimitComparison_cospan_leftFibration_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H) :=
  bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence H
    (limit.cone H) (limit.isLimit H)

/-- 概要：Hom 図式の左脚が fibration の豊穣極限の実際の q_x はホモトピー同値。
方針：実際の sHom の極限錐へ一脚の cospan の比較を適用する。
規約：Hom 図式の極限性と中央・右端の Kan 性および左脚の Fibration 性を明示する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の極限錐の検出への入力。 -/
lemma representableHomotopyLimitComparison_cospan_leftFibration_homotopyEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x))
    [KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).obj (AsSmall.up.obj .one))]
    [KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).obj (AsSmall.up.obj .right))]
    [Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) :=
  bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x) hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
