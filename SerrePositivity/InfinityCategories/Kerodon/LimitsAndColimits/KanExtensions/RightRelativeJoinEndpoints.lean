module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightRelativeJoinRealization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinEndpoints

/-!
概要：右相対 join 表示の両端を一つの比較から同時に指定する。
方針：C と K の明示的な直和を相対 join と右円柱へ写す。
規約：δ の単射性は仮定せず、両端包含の単射性を使う。
使われ方：右相対 join の端点補正と指定変換の類の追跡。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：右 relative join の C と K の端点をまとめる包含。
方針：両端への射を直和から貼る。
規約：左が C、右が K。
使われ方：両端の同時の厳密化の始域。 -/
def kanRightRelativeJoinEndpointInclusion {K C : SSet.{u}} (δ : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram C K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ)

/-- 概要：右両端包含は通常の join への射影により標準の両端包含になる。
方針：両射影の計算を直和でまとめる。
規約：全単体での射の等式。
使われ方：両端包含の単射性。 -/
lemma kanRightRelativeJoinEndpointInclusion_fst {K C : SSet.{u}} (δ : K ⟶ C) :
    kanRightRelativeJoinEndpointInclusion δ ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 C) δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion C K := by
  rw [kanRightRelativeJoinEndpointInclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanJoinEndpointDesc_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst]
  rfl

/-- 概要：右 relative join の両端包含は単射。
方針：通常の join の単射な両端包含への合成で検査する。
規約：δ 自体の単射性は不要。
使われ方：両端上の一つの同型の延長。 -/
instance kanRightRelativeJoinEndpointInclusion_mono {K C : SSet.{u}} (δ : K ⟶ C) :
    Mono (kanRightRelativeJoinEndpointInclusion δ) :=
  mono_of_mono_fac (kanRightRelativeJoinEndpointInclusion_fst δ)

/-- 概要：右円柱の底 C と prism の終点 K をまとめる射。
方針：底への包含と prism の時刻一を直和から貼る。
規約：始点の K は δ に沿う C 側で既に表されている。
使われ方：一つの円柱比較を両端へ同時に制限する。 -/
def kanRightCylinderEndpointInclusion {K C : SSet.{u}} (δ : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram C K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRightCylinder δ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderBase δ) (SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism δ)

/-- 概要：右円柱と相対 join の両端包含は比較射と可換。
方針：底の制限と標準右 prism の終点を計算する。
規約：左右は一つの等式にまとめる。
使われ方：両端同型の同時の輸送。 -/
lemma kanRightCylinderEndpointInclusion_comparison {K C : SSet.{u}} (δ : K ⟶ C) :
    kanRightCylinderEndpointInclusion δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinCylinderComparison δ =
      kanRightRelativeJoinEndpointInclusion δ := by
  rw [kanRightCylinderEndpointInclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanJoinEndpointDesc_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderBase_comparison, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism_comparison,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism_one]
  rfl

/-- 概要：右円柱図式の両端は元の F と F₀ に厳密に等しい。
方針：底の図式の回収と prism の終端を計算する。
規約：順序は F、F₀。
使われ方：両端同型の一つの標的の指定。 -/
lemma kanRightCylinderEndpointInclusion_diagram {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀) :
    kanRightCylinderEndpointInclusion δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCylinderDiagram δ F₀ F α =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F F₀ := by
  rw [kanRightCylinderEndpointInclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanJoinEndpointDesc_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderBase_diagram, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism_diagram, α.h₁]

/-- 概要：右円柱比較から得る両端同時の関手の同型。
方針：一つの円柱比較を直和の包含へ前合成し、厳密な制限式で輸送する。
規約：左右の同型を独立には選ばない。
使われ方：両端を厳密に固定する同型の延長。 -/
def RightKanRelativeJoinRealization.endpointsIso {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (kanRightRelativeJoinEndpointInclusion δ ≫ s.diagram) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F F₀) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoTransport (s.comparison.precomp (kanRightCylinderEndpointInclusion δ))
    (by rw [← Category.assoc, kanRightCylinderEndpointInclusion_comparison])
    (kanRightCylinderEndpointInclusion_diagram δ F₀ F α)

/-- 概要：両端同型の射は円柱比較の制限の射と同じ Arrow の類を持つ。
方針：端点の表示を輸送する一般補題を適用する。
規約：型付き端点が異なるので Arrow として比較する。
使われ方：補正正方形の側辺の類の比較。 -/
lemma RightKanRelativeJoinRealization.endpointsIso_hom_arrow {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :
    Arrow.mk s.endpointsIso.hom =
      Arrow.mk (s.comparison.precomp (kanRightCylinderEndpointInclusion δ)).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoTransport_hom_arrow _ _ _

/-- 概要：両端同型の代表と円柱比較の代表の制限は同じ h Fun の射を表す。
方針：選んだ代表を元の同型の射に戻し、前合成を保つ。
規約：代表そのものの raw な一致は仮定しない。
使われ方：二つの補正経路の側辺の同定。 -/
lemma RightKanRelativeJoinRealization.endpointsHomotopy_hom_arrow {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy s.endpointsIso.simplicialHomotopy)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
          s.comparison.simplicialHomotopy (kanRightCylinderEndpointInclusion δ)))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIso_simplicialHomotopy_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIso_simplicialHomotopy_hom]
  exact s.endpointsIso_hom_arrow

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
