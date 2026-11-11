module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRealization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointMaps
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：相対 join の両端を同時に指定する単射と写像円柱上の対応する射。
方針：左右の明示的な直和を使い、通常の join への単射で単射性を検査する。
規約：δ は任意。δ 自体の単射性は使わない。
使われ方：相対 join 表示の端点を厳密に固定する同型の延長。

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

/-- 概要：両端図式からの貼り合わせは後合成と可換。
方針：次数ごとの直和の各因子で計算する。
規約：全ての単体集合に成立する。
使われ方：両端の同時の指定の計算。 -/
lemma kanJoinEndpointDesc_comp {A B X Y : SSet.{u}} (f : A ⟶ X) (g : B ⟶ X) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc f g ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (f ≫ q) (g ≫ q) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  cases z <;> rfl

/-- 概要：相対 join の二つの端点をまとめた包含。
方針：両端図式の左右の射を相対 join の包含にする。
規約：左右は次数ごとの直和として交わらない。
使われ方：端点を同時に固定する延長の始域。 -/
def kanRelativeJoinEndpointInclusion {K C : SSet.{u}} (δ : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram K C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C))

/-- 概要：相対 join の両端包含は通常の join への射影と両立する。
方針：左右の射影の計算をまとめる。
規約：δ に充填性を仮定しない。
使われ方：両端包含の単射性。 -/
lemma kanRelativeJoinEndpointInclusion_fst {K C : SSet.{u}} (δ : K ⟶ C) :
    kanRelativeJoinEndpointInclusion δ ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap δ (𝟙 C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion K C := by
  rw [kanRelativeJoinEndpointInclusion, kanJoinEndpointDesc_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst]
  rfl

/-- 概要：相対 join の両端を同時に含める射は単射。
方針：通常の join の両端包含への合成が単射であることを使う。
規約：δ の単射性は不要。
使われ方：両端を厳密に固定する同型の延長。 -/
instance kanRelativeJoinEndpointInclusion_mono {K C : SSet.{u}} (δ : K ⟶ C) :
    Mono (kanRelativeJoinEndpointInclusion δ) :=
  mono_of_mono_fac (kanRelativeJoinEndpointInclusion_fst δ)

/-- 概要：写像円柱の始点 K と右端 C をまとめた射。
方針：K は prism の零端へ、C は pushout の右因子へ入れる。
規約：δ は任意。
使われ方：円柱比較同型を両端へ同時に制限する。 -/
def kanCylinderEndpointInclusion {K C : SSet.{u}} (δ : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram K C ⟶ pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) δ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) δ)
    (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) δ)

/-- 概要：写像円柱と相対 join の両端の射は比較射で両立する。
方針：prism の零端と相対 join の左端の一致を使う。
規約：射の厳密な等式。
使われ方：両端固定の同型を一つの比較から取り出す。 -/
lemma kanCylinderEndpointInclusion_comparison {K C : SSet.{u}} (δ : K ⟶ C) :
    kanCylinderEndpointInclusion δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison δ =
      kanRelativeJoinEndpointInclusion δ := by
  rw [kanCylinderEndpointInclusion, kanJoinEndpointDesc_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inl, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_zero]
  rfl

/-- 概要：左指定自然変換を貼った円柱の両端は元の二図式である。
方針：pushout の制限と β の始端を計算する。
規約：左右を一つの両端図式として固定する。
使われ方：相対 join 表示の端点の厳密化への入力。 -/
lemma kanCylinderEndpointInclusion_leftKanCylinderDiagram {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)) :
    kanCylinderEndpointInclusion δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCylinderDiagram δ F₀ F β =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F₀ F := by
  rw [kanCylinderEndpointInclusion, kanJoinEndpointDesc_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCylinderDiagram, pushout.inl_desc, pushout.inr_desc,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding, β.h₀]

/-- 概要：相対 join 表示の比較から両端を同時に指定した自然同型を得る。
方針：円柱全体の同型を両端図式へ制限する。
規約：左右の同型を別々には選ばない。
使われ方：単射に沿う同型の延長による厳密化。 -/
def LeftKanRelativeJoinRealization.endpointsIso {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (kanRelativeJoinEndpointInclusion δ ≫ s.diagram) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F₀ F) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoTransport (s.comparison.precomp (kanCylinderEndpointInclusion δ))
    (by rw [← Category.assoc, kanCylinderEndpointInclusion_comparison])
    (kanCylinderEndpointInclusion_leftKanCylinderDiagram δ F₀ F β)

/-- 概要：両端同型の射は円柱比較の前合成の射を端点だけ書き換えたもの。
方針：一般の同型の輸送の Arrow 比較を適用する。
規約：選んだ代表の raw な一致は使わない。
使われ方：補正正方形の左右の辺の類の一致。 -/
lemma LeftKanRelativeJoinRealization.endpointsIso_hom_arrow {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β) :
    Arrow.mk s.endpointsIso.hom =
      Arrow.mk (s.comparison.precomp (kanCylinderEndpointInclusion δ)).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoTransport_hom_arrow _ _ _

/-- 概要：両端同型の代表と円柱比較の代表の制限は同じ h Fun の射を表す。
方針：それぞれの代表の類を同型の射に戻し、端点の輸送を吸収する。
規約：端点の型付き表示が異なるため Arrow で述べる。
使われ方：二つの補正正方形の側辺の比較。 -/
lemma LeftKanRelativeJoinRealization.endpointsHomotopy_hom_arrow {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy s.endpointsIso.simplicialHomotopy)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
          s.comparison.simplicialHomotopy (kanCylinderEndpointInclusion δ)))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIso_simplicialHomotopy_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIso_simplicialHomotopy_hom]
  exact s.endpointsIso_hom_arrow

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
