module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftMappingArrowFamilies
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantUnitFormula

/-!
概要：F(x)→y の coherent な矢印の族から x→G(y) の族への比較。
方針：二つの端点の射影と両立する単体集合の射として全パラメータの比較を保持する。
規約：単位や余単位、各点での同値性はフィールドに含めない。
使われ方：B1 の自然な写像空間対応から単位を取り出す具体的な模型の準備。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：全単体的な矢印の族に作用する、端点を保った比較。
方針：F(x)→y の空間から x→G(y) の comma へ射を与え、二つの端点の射影を保つ。
規約：点ごとの任意の同値の族だけではこのデータを与えたことにならない。
使われ方：恒等矢印の族の像から自然な単位を構成する。 -/
structure MappingArrowComparison {X Y : SSet.{u}} (F : X ⟶ Y) (G : Y ⟶ X) where
  map : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G
  source : map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F
  target : map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F

namespace MappingArrowComparison
variable {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
variable (q : MappingArrowComparison F G)

/-- 概要：恒等矢印の族を比較で写した単位の図式。
方針：F(x) の恒等矢印の族を一つの単体的な射で写す。
規約：各点の単位を独立に選ばない。
使われ方：自然な単位のホモトピー代表。 -/
def unitDiagram : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily F ≫ q.map

/-- 概要：単位の図式の始域は恒等関手。
方針：比較の始域条件と恒等矢印の族の始域の回収。
規約：厳密な射の等式。使われ方：単位の始点。 -/
lemma unitDiagram_source : q.unitDiagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = 𝟙 X := by
  rw [unitDiagram, Category.assoc, q.source, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily_source]

/-- 概要：単位の図式の標的は F。
方針：比較の標的条件と恒等矢印の族の標的の回収。
規約：厳密な射の等式。使われ方：単位の終点。 -/
lemma unitDiagram_target : q.unitDiagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = F := by
  rw [unitDiagram, Category.assoc, q.target, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily_target]

/-- 概要：比較の恒等矢印での像は自然な単位のホモトピーを与える。
方針：単位の図式の comma 表示を展開し両端を正規化する。
規約：自然性は図式全体から来る。単位を入力に含めない。
使われ方：指定単位の局所判定へ渡す単位候補。 -/
def unitHomotopy : SSet.Homotopy (𝟙 X) (F ≫ G) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy q.unitDiagram).h
  h₀ := by rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy q.unitDiagram).h₀, q.unitDiagram_source]; rfl
  h₁ := by rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy q.unitDiagram).h₁, q.unitDiagram_target]; rfl
  rel := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy q.unitDiagram).rel

/-- 概要：矢印の比較から構成した自然な単位候補の h Fun の類。
方針：同じ図式から得たホモトピーの辺の類を取る。
規約：この段階では随伴の単位であるとは主張しない。
使われ方：各点の同値条件との照合の対象。 -/
def unitHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G) :=
  SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy q.unitHomotopy)

/-- 概要：比較の単位の各点の評価は同じ図式のホモトピーの成分。
方針：ホモトピーの h Fun の類の評価公式を使う。
規約：代表の選び直しはしない。
使われ方：写像空間の標準単位比較との局所照合。 -/
lemma unitHom_component (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent q.unitHom x = SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge q.unitHomotopy x).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy q.unitHomotopy x

/-- 概要：比較は非定値の両端を持つ任意のホモトピーの族に作用する。
方針：矢印空間へ持ち上げて比較で写し、comma のホモトピーへ戻す。
規約：ホモトピー類を経由せず、単位の普遍性も仮定しない。
使われ方：入力の自然な比較と構成した単位を照合する。 -/
def mapHomotopy {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ Y)
    (H : SSet.Homotopy (a ≫ F) b) : SSet.Homotopy a (b ≫ G) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H ≫ q.map)).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H ≫ q.map)).h₀,
      Category.assoc, q.source, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_source]
    rfl
  h₁ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H ≫ q.map)).h₁]
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H ≫ q.map) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) ≫ G = b ≫ G
    apply congrArg (fun f => f ≫ G)
    rw [Category.assoc, q.target, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_target]
  rel := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H ≫ q.map)).rel

/-- 概要：比較の族への作用は任意のパラメータの前合成と可換。
方針：矢印の族の持ち上げと comma の表示の前合成自然性を使う。
規約：raw なホモトピーの射の等式。
使われ方：各点の比較を独立に選んだ族と区別する。 -/
lemma mapHomotopy_precomp_h {A B : SSet.{u}} (i : A ⟶ B)
    (a : B ⟶ X) (b : B ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    (q.mapHomotopy (i ≫ a) (i ≫ b) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i)).h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (q.mapHomotopy a b H).h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F (i ≫ a) (i ≫ b)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i) ≫ q.map)).h = _
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy ((i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H) ≫ q.map)).h :=
      congrArg (fun f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (f ≫ q.map)).h)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_precomp F i a b H)
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H ≫ q.map)

end MappingArrowComparison
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
