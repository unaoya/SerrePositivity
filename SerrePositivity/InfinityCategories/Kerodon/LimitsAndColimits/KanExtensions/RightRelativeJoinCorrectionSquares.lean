module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightRelativeJoinStrictification
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinConeTransport
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrismHomotopySquare

/-!
概要：右相対 join の円柱比較と端点補正を共通の下辺を持つ正方形で表す。
方針：右 prism の時間を第一因子へ直し、保持したホモトピーを制限して転置する。
規約：左辺は C 側の補正の δ に沿う制限、右辺は K 側の補正。
使われ方：補正後の右指定変換と元の α の類の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：補正前の右相対 join 図式の標準指定変換。
方針：既存の標準右変換を取る。
規約：両端は補正前の図式の制限。
使われ方：二つの補正正方形の共通の下辺。 -/
def RightKanRelativeJoinRealization.prismTransformation {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :
    SSet.Homotopy (δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ ≫ s.diagram)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ ≫ s.diagram) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightTransformation δ s.diagram

/-- 概要：一つの円柱比較の代表を prism 全体へ制限する。
方針：時間を第一因子へ直した右円柱 prism に前合成する。
規約：制限後に代表を選び直さない。
使われ方：元の α を上辺に持つ正方形。 -/
def RightKanRelativeJoinRealization.comparisonPrismHomotopy {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :
    SSet.Homotopy ((β_ (Δ[1] : SSet.{u}) K).hom ≫ s.prismTransformation.h)
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ α.h) where
  h := (((β_ (Δ[1] : SSet.{u}) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism δ) ▷ Δ[1]) ≫
    s.comparison.simplicialHomotopy.h
  h₀ := by
    rw [SSet.ι₀_comp_assoc, s.comparison.simplicialHomotopy.h₀]
    simp only [Category.assoc, prismTransformation, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightTransformation]
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism δ), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism_comparison]
    rfl
  h₁ := by
    rw [SSet.ι₁_comp_assoc, s.comparison.simplicialHomotopy.h₁]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism_diagram]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：一つの端点補正を右 prism 上へ制限する。
方針：右 prism を時間第一因子で表示し、実際の延長ホモトピーを前合成する。
規約：上辺は補正後の指定変換そのもの。
使われ方：円柱比較の正方形と比較する第二の正方形。 -/
def RightKanRelativeJoinRealization.Strictification.correctionPrismHomotopy
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification) :
    SSet.Homotopy ((β_ (Δ[1] : SSet.{u}) K).hom ≫ s.prismTransformation.h)
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ r.transformation.h) where
  h := (((β_ (Δ[1] : SSet.{u}) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ) ▷ Δ[1]) ≫
    (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ) (Δ[1] : SSet.{u})).hom ≫ r.homotopy
  h₀ := by
    rw [SSet.ι₀_comp_assoc]
    change ((β_ (Δ[1] : SSet.{u}) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ) ≫ r.homotopy) = _
    rw [r.start]
    rfl
  h₁ := by
    rw [SSet.ι₁_comp_assoc]
    change ((β_ (Δ[1] : SSet.{u}) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ) ≫ r.homotopy) = _
    rw [r.finish]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：右円柱比較を指定四辺を持つ関手正方形へ転置する。
方針：一般の prism ホモトピーの正方形を使う。
規約：側辺も同じ比較の代表から得る。
使われ方：補正の正方形との類の比較。 -/
def RightKanRelativeJoinRealization.comparisonSquare {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare s.prismTransformation α
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyLeft s.prismTransformation α s.comparisonPrismHomotopy)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyRight s.prismTransformation α s.comparisonPrismHomotopy) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopySquare s.prismTransformation α s.comparisonPrismHomotopy

/-- 概要：右端点補正を指定四辺を持つ関手正方形へ転置する。
方針：実際の補正 prism を一般の正方形へ渡す。
規約：円柱比較と共通の下辺を持つ。
使われ方：同じ側辺の類から上辺の類を同定する。 -/
def RightKanRelativeJoinRealization.Strictification.correctionSquare
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare s.prismTransformation r.transformation
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyLeft s.prismTransformation r.transformation r.correctionPrismHomotopy)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyRight s.prismTransformation r.transformation r.correctionPrismHomotopy) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopySquare s.prismTransformation r.transformation r.correctionPrismHomotopy

/-- 概要：補正の左辺は C 側の端点同型の δ に沿う制限。
方針：右 prism の始端を計算し、保持した fixed の式を使う。
規約：代表の選び直しを行わない。
使われ方：二つの左側辺の類の比較。 -/
lemma RightKanRelativeJoinRealization.Strictification.correctionSquare_left_h
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyLeft s.prismTransformation r.transformation r.correctionPrismHomotopy).h =
      ((δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K) ▷ (Δ[1] : SSet.{u})) ≫
        s.endpointsIso.simplicialHomotopy.h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
    (((β_ (Δ[1] : SSet.{u}) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ) ▷ Δ[1]) ≫
    (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ) (Δ[1] : SSet.{u})).hom ≫ r.homotopy = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ ((β_ (Δ[1] : SSet.{u}) K).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ) = δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism_zero]
  rw [hp]
  have h : ((δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ) ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ) (Δ[1] : SSet.{u})).hom =
      ((δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K) ▷ (Δ[1] : SSet.{u})) ≫
        (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram C K) (Δ[1] : SSet.{u})).hom ≫
        ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinEndpointInclusion δ) := rfl
  rw [← Category.assoc, h, Category.assoc, Category.assoc, r.fixed]
  simp only [SymmetricCategory.symmetry_assoc]

/-- 概要：比較の左辺は右円柱の底の代表の δ に沿う制限。
方針：円柱 prism の始点の貼り合わせを使う。
規約：元の比較の一つの代表を保持する。
使われ方：端点補正の左辺との類の比較。 -/
lemma RightKanRelativeJoinRealization.comparisonSquare_left_h {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyLeft s.prismTransformation α s.comparisonPrismHomotopy).h =
      ((δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderBase δ) ▷ (Δ[1] : SSet.{u})) ≫
        s.comparison.simplicialHomotopy.h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
    (((β_ (Δ[1] : SSet.{u}) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism δ) ▷ Δ[1]) ≫ _ = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism_zero]

/-- 概要：補正の右辺は K 側の端点同型の制限。
方針：右 prism の終端と fixed の式を使う。
規約：右辺には δ の前合成は入らない。
使われ方：二つの右側辺の類の比較。 -/
lemma RightKanRelativeJoinRealization.Strictification.correctionSquare_right_h
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α} (r : s.Strictification) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyRight s.prismTransformation r.transformation r.correctionPrismHomotopy).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr C K ▷ (Δ[1] : SSet.{u})) ≫ s.endpointsIso.simplicialHomotopy.h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
    (((β_ (Δ[1] : SSet.{u}) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ) ▷ Δ[1]) ≫
    (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ) (Δ[1] : SSet.{u})).hom ≫ r.homotopy = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ ((β_ (Δ[1] : SSet.{u}) K).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism_one]
  rw [hp]
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ) (Δ[1] : SSet.{u})).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr C K ▷ (Δ[1] : SSet.{u})) ≫
        (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram C K) (Δ[1] : SSet.{u})).hom ≫
        ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinEndpointInclusion δ) := rfl
  rw [← Category.assoc, h, Category.assoc, Category.assoc, r.fixed]
  simp only [SymmetricCategory.symmetry_assoc]

/-- 概要：比較の右辺は右円柱 prism の終端での代表の制限。
方針：二回の前合成をまとめて時間の終端を直す。
規約：円柱比較の一つの代表を保持する。
使われ方：端点補正の右辺との類の比較。 -/
lemma RightKanRelativeJoinRealization.comparisonSquare_right_h {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.prismHomotopyRight s.prismTransformation α s.comparisonPrismHomotopy).h =
      ((SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism δ) ▷ (Δ[1] : SSet.{u})) ≫
        s.comparison.simplicialHomotopy.h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
    (((β_ (Δ[1] : SSet.{u}) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCylinderPrism δ) ▷ Δ[1]) ≫ _ = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
