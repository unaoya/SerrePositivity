module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinStrictification
public import SerrePositivity.InfinityCategories.F1B.KanPrismHomotopySquare

/-!
概要：相対 join の円柱比較と厳密化の補正を、共通の下辺を持つ正方形で表示する。
方針：元の図式の prism を下辺とし、それぞれの補正ホモトピーを制限する。
規約：このファイルの正方形の構成だけでは左右の辺の類の一致を主張しない。
使われ方：厳密化後の指定自然変換の h Fun の類を元の変換と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対 join 表示の元の図式から得る指定自然変換。
方針：標準 prism を図式に写す。
規約：端点は補正前の図式の制限。
使われ方：二つの補正正方形の共通の下辺。 -/
def LeftKanRelativeJoinRealization.prismTransformation {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (s : LeftKanRelativeJoinRealization δ F₀ F β) :
    SSet.Homotopy (relativeJoinInl δ (𝟙 C) ≫ s.diagram)
      (δ ≫ relativeJoinInr δ (𝟙 C) ≫ s.diagram) where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ relativeJoinPrism δ ≫ s.diagram
  h₀ := by
    rw [← Category.assoc]
    change prismEndpoint 0 K ≫ relativeJoinPrism δ ≫ s.diagram = _
    rw [← Category.assoc, relativeJoinPrism_zero]
    rfl
  h₁ := by
    rw [← Category.assoc]
    change prismEndpoint 1 K ≫ relativeJoinPrism δ ≫ s.diagram = _
    rw [← Category.assoc, relativeJoinPrism_one, Category.assoc]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：円柱全体の比較を prism 上へ制限した補正ホモトピー。
方針：比較同型の代表を pushout の左因子へ前合成する。
規約：代表を制限した後に別の代表を選び直さない。
使われ方：元の β を上辺に持つ正方形。 -/
def LeftKanRelativeJoinRealization.comparisonPrismHomotopy {K C D : SSet.{u}}
    [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (s : LeftKanRelativeJoinRealization δ F₀ F β) :
    SSet.Homotopy ((β_ (Δ[1] : SSet.{u}) K).hom ≫ s.prismTransformation.h)
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ β.h) where
  h := (pushout.inl (prismEndpoint 1 K) δ ▷ (Δ[1] : SSet.{u})) ≫
    s.comparison.simplicialHomotopy.h
  h₀ := by
    rw [SSet.ι₀_comp_assoc, s.comparison.simplicialHomotopy.h₀,
      ← Category.assoc, relativeJoinCylinderComparison_inl]
    simp only [prismTransformation, ← Category.assoc, SymmetricCategory.symmetry,
      Category.id_comp]
    rfl
  h₁ := by
    rw [SSet.ι₁_comp_assoc, s.comparison.simplicialHomotopy.h₁,
      leftKanCylinderDiagram, pushout.inl_desc]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：端点の厳密化の補正を prism 上へ制限したホモトピー。
方針：保持した補正を時間第二因子に転置し、標準 prism へ前合成する。
規約：上辺は補正後の指定自然変換そのもの。
使われ方：円柱比較の正方形と比較する第二の正方形。 -/
def LeftKanRelativeJoinRealization.Strictification.correctionPrismHomotopy
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    SSet.Homotopy ((β_ (Δ[1] : SSet.{u}) K).hom ≫ s.prismTransformation.h)
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ r.transformation.h) where
  h := (relativeJoinPrism δ ▷ (Δ[1] : SSet.{u})) ≫
    (β_ (relativeJoin δ (𝟙 C)) (Δ[1] : SSet.{u})).hom ≫ r.homotopy
  h₀ := by
    rw [SSet.ι₀_comp_assoc]
    change relativeJoinPrism δ ≫ (prismEndpoint 0 (relativeJoin δ (𝟙 C)) ≫ r.homotopy) = _
    rw [r.start]
    simp only [prismTransformation, ← Category.assoc, SymmetricCategory.symmetry,
      Category.id_comp]
    rfl
  h₁ := by
    rw [SSet.ι₁_comp_assoc]
    change relativeJoinPrism δ ≫ (prismEndpoint 1 (relativeJoin δ (𝟙 C)) ≫ r.homotopy) = _
    rw [r.finish]
    simp only [transformation, ← Category.assoc, SymmetricCategory.symmetry,
      Category.id_comp]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：円柱比較は元の指定変換を上辺に持つ正方形を与える。
方針：prism 上へ制限した比較ホモトピーを転置する。
規約：左右の辺もこの同じ比較ホモトピーから得る。
使われ方：補正後の正方形との h Fun での比較。 -/
def LeftKanRelativeJoinRealization.comparisonSquare {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} (s : LeftKanRelativeJoinRealization δ F₀ F β) :
    KanFunctorHomSquare s.prismTransformation β
      (kanPrismHomotopyLeft s.prismTransformation β s.comparisonPrismHomotopy)
      (kanPrismHomotopyRight s.prismTransformation β s.comparisonPrismHomotopy) :=
  kanPrismHomotopySquare s.prismTransformation β s.comparisonPrismHomotopy

/-- 概要：端点の厳密化は補正後の変換を上辺に持つ正方形を与える。
方針：保持した補正ホモトピーを prism に制限して転置する。
規約：円柱比較の正方形と下辺が厳密に同じ。
使われ方：側辺の類を比較した後で上辺の類を同定する。 -/
def LeftKanRelativeJoinRealization.Strictification.correctionSquare
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    KanFunctorHomSquare s.prismTransformation r.transformation
      (kanPrismHomotopyLeft s.prismTransformation r.transformation r.correctionPrismHomotopy)
      (kanPrismHomotopyRight s.prismTransformation r.transformation r.correctionPrismHomotopy) :=
  kanPrismHomotopySquare s.prismTransformation r.transformation r.correctionPrismHomotopy

/-- 概要：厳密化の正方形の左辺は、両端同型の選んだ代表の左制限。
方針：prism の零端を計算し、保持した fixed の式に帰着する。
規約：円柱全体の代表の制限との raw な一致は主張しない。
使われ方：二つの左辺の類を前合成の自然性で比較する。 -/
lemma LeftKanRelativeJoinRealization.Strictification.correctionSquare_left_h
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    (kanPrismHomotopyLeft s.prismTransformation r.transformation
      r.correctionPrismHomotopy).h =
      (joinEndpointInl K C ▷ (Δ[1] : SSet.{u})) ≫ s.endpointsIso.simplicialHomotopy.h := by
  change (prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
    (relativeJoinPrism δ ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (relativeJoin δ (𝟙 C)) (Δ[1] : SSet.{u})).hom ≫ r.homotopy = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, relativeJoinPrism_zero]
  have h : (relativeJoinInl δ (𝟙 C) ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (relativeJoin δ (𝟙 C)) (Δ[1] : SSet.{u})).hom =
      (joinEndpointInl K C ▷ (Δ[1] : SSet.{u})) ≫
        (β_ (joinEndpointDiagram K C) (Δ[1] : SSet.{u})).hom ≫
        ((Δ[1] : SSet.{u}) ◁ kanRelativeJoinEndpointInclusion δ) := rfl
  rw [← Category.assoc, h, Category.assoc, Category.assoc, r.fixed]
  simp only [SymmetricCategory.symmetry_assoc]

/-- 概要：円柱比較の正方形の左辺は、円柱比較の代表の始端での制限。
方針：二回の前合成を一回にまとめる。
規約：代表は選び直さない。
使われ方：端点同型の前合成の類との比較。 -/
lemma LeftKanRelativeJoinRealization.comparisonSquare_left_h {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} (s : LeftKanRelativeJoinRealization δ F₀ F β) :
    (kanPrismHomotopyLeft s.prismTransformation β s.comparisonPrismHomotopy).h =
      ((prismEndpoint 0 K ≫ pushout.inl (prismEndpoint 1 K) δ) ▷
        (Δ[1] : SSet.{u})) ≫ s.comparison.simplicialHomotopy.h := by
  change (prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
    (pushout.inl (prismEndpoint 1 K) δ ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight]

/-- 概要：厳密化の正方形の右辺は両端同型の右制限の δ に沿う前合成。
方針：prism の一端を計算して fixed の式を適用する。
規約：右辺の始域は K。
使われ方：二つの正方形の右辺の類の比較。 -/
lemma LeftKanRelativeJoinRealization.Strictification.correctionSquare_right_h
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    (kanPrismHomotopyRight s.prismTransformation r.transformation
      r.correctionPrismHomotopy).h =
      ((δ ≫ joinEndpointInr K C) ▷ (Δ[1] : SSet.{u})) ≫
        s.endpointsIso.simplicialHomotopy.h := by
  change (prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
    (relativeJoinPrism δ ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (relativeJoin δ (𝟙 C)) (Δ[1] : SSet.{u})).hom ≫ r.homotopy = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, relativeJoinPrism_one]
  have h : ((δ ≫ relativeJoinInr δ (𝟙 C)) ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (relativeJoin δ (𝟙 C)) (Δ[1] : SSet.{u})).hom =
      ((δ ≫ joinEndpointInr K C) ▷ (Δ[1] : SSet.{u})) ≫
        (β_ (joinEndpointDiagram K C) (Δ[1] : SSet.{u})).hom ≫
        ((Δ[1] : SSet.{u}) ◁ kanRelativeJoinEndpointInclusion δ) := rfl
  rw [← Category.assoc, h, Category.assoc, Category.assoc, r.fixed]
  simp only [SymmetricCategory.symmetry_assoc]

/-- 概要：円柱比較の正方形の右辺は比較の右端制限の δ に沿う前合成。
方針：prism の一端の貼り合わせ条件を使う。
規約：同じ円柱比較の代表を保持する。
使われ方：両端同型の類の前合成との同定。 -/
lemma LeftKanRelativeJoinRealization.comparisonSquare_right_h {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} (s : LeftKanRelativeJoinRealization δ F₀ F β) :
    (kanPrismHomotopyRight s.prismTransformation β s.comparisonPrismHomotopy).h =
      ((δ ≫ pushout.inr (prismEndpoint 1 K) δ) ▷ (Δ[1] : SSet.{u})) ≫
        s.comparison.simplicialHomotopy.h := by
  change (prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
    (pushout.inl (prismEndpoint 1 K) δ ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, pushout.condition]

end SerrePositivity.InfinityCategories
