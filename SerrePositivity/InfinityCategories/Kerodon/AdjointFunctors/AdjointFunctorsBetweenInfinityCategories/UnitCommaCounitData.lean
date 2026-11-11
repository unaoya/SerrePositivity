module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCounitExistence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaHomotopySquare

/-!
概要：comma 内の比較と、同じ比較から射影した余単位を一つのデータとして保持する。
方針：基底固定の比較を保持し、標的への射影で余単位のホモトピーと類を定める。
規約：余単位や三角恒等式を独立に選び直さない。
使われ方：B1 の指定単位と構成した余単位の三角恒等式の検証。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：基底固定の comma 内の余単位比較。
方針：G に沿った単位切断から恒等矢印の族への実際のホモトピーを保持する。
規約：三角恒等式はフィールドに含めない。
使われ方：選んだ比較と余単位の関係を保持する。 -/
structure UnitCommaCounitData {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) where
  comparison : SSet.Homotopy (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily G)
  over_source : comparison.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = fst Y (Δ[1] : SSet.{u}) ≫ G

/-- 概要：各点の単位比較条件は基底固定の余単位比較データを与える。
方針：構成済みの comma 比較の存在を束ねる。
規約：追加の輸送や三角恒等式は要求しない。
使われ方：指定単位から随伴を構成する際の選択。 -/
lemma UnitMappingSpaceCondition.nonempty_counitData
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) : Nonempty (UnitCommaCounitData η) := by
  obtain ⟨H, hH⟩ := hη.exists_counitComparison
  exact ⟨⟨H, hH⟩⟩

namespace UnitCommaCounitData
variable {X Y : SSet.{u}} [Quasicategory X]
variable {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
variable (c : UnitCommaCounitData η)

/-- 概要：保持した比較から取り出した余単位のホモトピー。
方針：標的へ射影して両端の関手を正規化する。
規約：raw な射は比較の射影そのもの。
使われ方：三角恒等式の上辺の代表。 -/
def counitHomotopy : SSet.Homotopy (G ≫ F) (𝟙 Y) where
  h := c.comparison.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G
  h₀ := by rw [← Category.assoc, c.comparison.h₀, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection_target]; rfl
  h₁ := by rw [← Category.assoc, c.comparison.h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily_target]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：比較から射影した余単位の h Fun の類。
方針：保持したホモトピーの辺の類を取る。
規約：三角恒等式は後で証明する。
使われ方：随伴データの余単位候補。 -/
def counitHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (G ≫ F) (𝟙 Y) :=
  SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy c.counitHomotopy)

/-- 概要：G に沿った指定単位のホモトピー代表。
方針：単位の選んだ代表を G に沿って前合成する。
規約：raw な射を保持して端点を正規化する。
使われ方：右三角恒等式の左辺の代表。 -/
def unitAlongG (_c : UnitCommaCounitData η) : SSet.Homotopy G ((G ≫ F) ≫ G) where
  h := (G ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η).h
  h₀ := by rw [SSet.ι₀_comp_assoc, (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η).h₀, Category.comp_id]; rfl
  h₁ := by rw [SSet.ι₁_comp_assoc, (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η).h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：余単位を G で後合成したホモトピー代表。
方針：余単位の raw な射を後合成して端点を正規化する。
規約：恒等関手の合成を正規化する。
使われ方：右三角恒等式の上辺。 -/
def counitAlongG : SSet.Homotopy ((G ≫ F) ≫ G) G where
  h := c.counitHomotopy.h ≫ G
  h₀ := by rw [← Category.assoc, c.counitHomotopy.h₀]; rfl
  h₁ := by rw [← Category.assoc, c.counitHomotopy.h₁, Category.id_comp]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：G に沿った指定単位の raw な代表は比較正方形の左辺。
方針：comma の持ち上げの回収と前合成自然性を使う。
規約：新しい単位代表を選ばない。
使われ方：右三角恒等式の四辺の照合。 -/
lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare c.comparison = curry c.unitAlongG.h := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp]
  change curry ((G ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G (𝟙 X) F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η))).h) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_lift_h]
  rfl

/-- 概要：比較正方形の右辺は恒等関手 G の時間に定値な代表。
方針：恒等矢印の族の定義と持ち上げの回収を使う。
規約：raw な代表の一致。
使われ方：右三角恒等式の恒等射。 -/
lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare c.comparison = curry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl G).h := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare_right]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_lift_h]
  rfl

/-- 概要：比較正方形の下辺は G の定値関手頂点。
方針：比較の基底固定条件を適用する。
規約：射影は全時間で定値。
使われ方：右三角恒等式の退化辺の消去。 -/
lemma square_bottom : SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare c.comparison =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare_bottom, c.over_source]
  apply uncurry_injective
  rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：比較正方形の上辺は余単位の G による像。
方針：余単位の射影の定義を展開する。
規約：同じ比較から得た余単位を使う。
使われ方：右三角恒等式の合成辺の照合。 -/
lemma square_top : SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare c.comparison =
    curry c.counitAlongG.h := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare_top]
  change curry (c.comparison.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G ≫ G) =
    curry ((c.comparison.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) ≫ G)
  rw [Category.assoc]

/-- 概要：保持した比較から得る単位と余単位の代表は右三角恒等式を満たす。
方針：下辺が恒等の正方形の合成関係に四辺の回収を渡す。
規約：h Fun 内の等式であり、各点の評価への忘却はしない。
使われ方：指定単位から随伴を構成する際の右三角恒等式。 -/
lemma right_triangle_representatives :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy c.unitAlongG) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy c.counitAlongG) =
        𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHom_comp_eq_of_square c.unitAlongG (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl G) c.counitAlongG
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare c.comparison) c.square_bottom c.square_top c.square_left c.square_right
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom G)

/-- 概要：右三角恒等式の単位の代表は G に沿った指定単位の前合成を表す。
方針：raw な代表の一致と前合成の一般公式を使う。
規約：h Fun の射の等式。使われ方：代表による式を whisker による式へ移す。 -/
lemma unitAlongG_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy c.unitAlongG) =
      (hoFunctor.map ((pre G).app X)).toFunctor.map η := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η) G
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom] at h
  exact h

/-- 概要：右三角恒等式の余単位の代表は G による後合成を表す。
方針：raw な代表の一致と後合成の一般公式を使う。
規約：h Fun の射の等式。使われ方：代表による式を whisker による式へ移す。 -/
lemma counitAlongG_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy c.counitAlongG) =
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map c.counitHom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom c.counitHomotopy G

/-- 概要：比較から構成した余単位は指定単位との右三角恒等式を h Fun 内で満たす。
方針：正方形から得た代表の合成を前後合成の作用へ移す。
規約：各点の評価での等式に弱めない。左三角恒等式は後続。
使われ方：指定単位と余単位から随伴データを構成する。 -/
lemma right_triangle :
    (hoFunctor.map ((pre G).app X)).toFunctor.map η ≫
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map c.counitHom =
        𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  rw [← c.unitAlongG_hom, ← c.counitAlongG_hom]
  exact c.right_triangle_representatives

end UnitCommaCounitData
/-- 概要：各点の単位比較条件から、指定単位との右三角恒等式を持つ自然な余単位が存在する。
方針：基底固定の比較データを一つ選び、同じ比較から得る余単位と正方形の関係を使う。
規約：左三角恒等式を仮定・結論しない。h Fun 内の右三角恒等式を保持する。
使われ方：B1 の局所存在判定で残る左三角恒等式の入力。 -/
lemma UnitMappingSpaceCondition.exists_counit_right_triangle
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) :
    ∃ ε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (G ≫ F) (𝟙 Y),
      (hoFunctor.map ((pre G).app X)).toFunctor.map η ≫
        (hoFunctor.map ((ihom Y).map G)).toFunctor.map ε =
          𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  let c : UnitCommaCounitData η := Classical.choice hη.nonempty_counitData
  exact ⟨c.counitHom, c.right_triangle⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
