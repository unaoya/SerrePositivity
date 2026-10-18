module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialNerveCorner
public import SerrePositivity.InfinityCategories.HomotopyLimits.CospanOverRight
public import SerrePositivity.InfinityCategories.HomotopyLimits.CospanSingleFibrationPointComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.RepresentableComparison

/-!
概要：中央と右端が Kan、左脚だけが fibration の cospan の実際の標準比較の同値性。
方針：元の重みの右遷移の anodyne 性を相対錐の境界へ移し、補助重みの二つの制限を使う。
規約：右脚の fibration 性も未証明の相対境界の条件も要求しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.3.12、7.5.4.6 の引き戻しの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：元の Bousfield–Kan 重みから補助重みへの包含の中央の相対境界は anodyne。
方針：右遷移の over 圏の nerve の anodyne 性を、始対象の付加の相対境界へ移す。
規約：AsSmall に持ち上げた cospan の実際の重みを使う。
使われ方：Kerodon 7.5.3.12 の一脚だけが fibration の標準比較の第二段階。 -/
lemma bousfieldKanConeWeightInclusion_cospan_corner_anodyne :
    anodyneExtensions (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up
      (bousfieldKanConeWeightInclusion (I := AsSmall.{u} WalkingCospan)))) := by
  have : (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_functor
  let r := (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).map
    WalkingCospan.Hom.inr
  have hm := bousfieldKanWeight_map_mono r
  have : Mono (nerveMap (Over.map r)) := hm
  exact initialNerveCorner_anodyne (Over.map r)
    bousfieldKanWeight_cospan_inr_anodyne

variable (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]

/-- 概要：補助重みから元の重みへの実際の制限は一脚の fibration 性で trivial Kan fibration。
方針：成分ごとの anodyne 性と実際に検証した中央の相対境界を使う。
規約：中央と右端の Kan 性および左脚の Fibration 性を要求する。
使われ方：Kerodon 7.5.3.12 の元の重み側の制限の同値性。 -/
lemma bousfieldKanConeWeightInclusion_cospan_leftFibration_trivialKanFibration :
    TrivialKanFibration (weightedSectionsPre bousfieldKanConeWeightInclusion H) :=
  weightedSectionsPre_cospan_leftFibration_trivialKanFibration
    bousfieldKanConeWeightInclusion bousfieldKanConeWeightInclusion_anodyne
    bousfieldKanConeWeightInclusion_cospan_corner_anodyne

/-- 概要：補助重みから元の重みへの実際の制限は一脚の fibration 性でホモトピー同値。
方針：両重みの右脚の単射性と、相対境界から得た制限の同値性を使う。
規約：右脚の fibration 性は要求しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の κ の分解の第二の射。 -/
lemma bousfieldKanConeWeightInclusion_cospan_leftFibration_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre bousfieldKanConeWeightInclusion H) := by
  have : (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_functor
  have := bousfieldKanWeight_map_mono (AsSmall.up.map WalkingCospan.Hom.inr)
  have := bousfieldKanConeWeight_map_mono (AsSmall.up.map WalkingCospan.Hom.inr)
  exact weightedSectionsPre_cospan_leftFibration_homotopyEquivalence
    bousfieldKanConeWeightInclusion bousfieldKanConeWeightInclusion_anodyne
    bousfieldKanConeWeightInclusion_cospan_corner_anodyne

/-- 概要：一脚が fibration の Kan cospan の任意の極限錐からの実際の標準比較は同値。
方針：strict 極限から補助 end への同値と、元の重みへの制限の同値を合成する。
規約：極限頂点の Kan 性は追加せず、中央と右端の Kan 性から導く。
使われ方：Kerodon 7.5.3.12 の引き戻しの homotopy 極限の比較。 -/
lemma bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
    (c : Cone H) (hc : IsLimit c) :
    IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison c) := by
  let U := (Functor.const (AsSmall.{u} WalkingCospan)).obj (Δ[0] : SSet.{u})
  have hU : IsTerminal U := weightIsTerminalOfObj U (fun _ => stdSimplex.isTerminalObj₀)
  have := weightedConeComparison_isIso_of_isTerminalWeight U hU c hc
  have : Mono (U.map (AsSmall.up.map WalkingCospan.Hom.inr)) :=
    inferInstanceAs (Mono (𝟙 (Δ[0] : SSet.{u})))
  have := weightedSections_cospan_leftFibration_kanComplex U H
  have := kanComplex_of_iso (asIso (weightedConeComparison U c)).symm
  have := bousfieldKanConeWeight_cospan_leftFibration_kanComplex H
  have := bousfieldKanHolim_cospan_leftFibration_kanComplex H
  rw [← bousfieldKanConeComparison_factorization c]
  exact (bousfieldKanConeWeightComparison_cospan_leftFibration_homotopyEquivalence H c hc).comp
    (bousfieldKanConeWeightInclusion_cospan_leftFibration_homotopyEquivalence H)

/-- 概要：一脚だけが fibration の cospan の選択された strict 極限からの実際の κ は同値。
方針：任意の極限錐の比較を選択された極限錐へ適用する。
規約：中央と右端が Kan、左脚が Fibration。右脚の条件は追加しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の引き戻しの比較。 -/
lemma bousfieldKanLimitComparison_cospan_leftFibration_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison H) :=
  bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence H
    (limit.cone H) (limit.isLimit H)

/-- 概要：Hom 図式の左脚が fibration の豊穣極限の実際の q_x はホモトピー同値。
方針：実際の sHom の極限錐へ一脚の cospan の比較を適用する。
規約：Hom 図式の極限性と中央・右端の Kan 性および左脚の Fibration 性を明示する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6 の極限錐の検出への入力。 -/
lemma representableHomotopyLimitComparison_cospan_leftFibration_homotopyEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj .one))]
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj .right))]
    [Fibration ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x) :=
  bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence _
    (simplicialHomCone c x) hc

end SerrePositivity.InfinityCategories.HomotopyLimits
