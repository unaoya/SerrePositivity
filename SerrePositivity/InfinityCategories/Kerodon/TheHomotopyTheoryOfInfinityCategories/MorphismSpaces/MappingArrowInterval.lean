module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameters
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilySquareInverse
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCompositionTriangle

/-!
概要：coherent な矢印比較を各点の区間写像空間へ制限する。
方針：定値端点の普遍族を矢印空間へ持ち上げ、比較の像を curry する。
規約：単位は入力に含めず、同値性もまだ仮定しない。
使われ方：B1 の自然な写像空間対応と指定単位版の局所判定の接続。

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

/-- 概要：定値端点の区間族を F(x)→y のホモトピーとして読む。
方針：既存の区間族の表示で始点を定値関手の後合成に正規化する。
規約：標的の quasicategory 性は不要。
使われ方：各点の写像空間から矢印空間への持ち上げ。 -/
def leftMappingIntervalHomotopy {A X Y : SSet.{u}} (F : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    SSet.Homotopy ((SSet.const x : A ⟶ X) ≫ F) (SSet.const y) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h
  h₀ := by rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h₀, SSet.const_comp]; rfl
  h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h₁
  rel := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).rel

/-- 概要：各点の区間族を coherent な矢印の空間へ持ち上げる。
方針：始域 x と標的 y を固定して族全体を持ち上げる。
規約：パラメータ A は任意。
使われ方：自然な比較の各点への制限。 -/
def leftMappingIntervalFamily {A X Y : SSet.{u}} (F : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F (SSet.const x) (SSet.const y) (leftMappingIntervalHomotopy F x y f)

/-- 概要：持ち上げた区間族の始域を回収する。
方針：矢印の持ち上げの射影公式。
規約：厳密な等式。使われ方：比較後の始点の計算。 -/
lemma leftMappingIntervalFamily_source {A X Y : SSet.{u}} (F : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    leftMappingIntervalFamily F x y f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F = SSet.const x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_source _ _ _ _

/-- 概要：持ち上げた区間族の標的を回収する。
方針：矢印の持ち上げの射影公式。
規約：厳密な等式。使われ方：比較後の終点の計算。 -/
lemma leftMappingIntervalFamily_target {A X Y : SSet.{u}} (F : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    leftMappingIntervalFamily F x y f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F = SSet.const y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_target _ _ _ _

/-- 概要：持ち上げた族をホモトピーとして読むと元の区間族になる。
方針：矢印の表示と持ち上げの往復を使う。
規約：raw な射の等式。使われ方：パラメータ自然性の検証。 -/
lemma leftMappingIntervalFamily_h {A X Y : SSet.{u}} (F : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy (leftMappingIntervalFamily F x y f)).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_homotopy_h _ _ _ _

/-- 概要：区間族の持ち上げは任意のパラメータ射に自然。
方針：始域・標的・raw なホモトピーで矢印の族を比較する。
規約：ホモトピー類に下ろす前の等式。
使われ方：各点への制限も一つの単体的な射で与えられることの証明。 -/
lemma leftMappingIntervalFamily_precomp {A B X Y : SSet.{u}} (F : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) (i : A ⟶ B)
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    leftMappingIntervalFamily F x y (i ≫ f) = i ≫ leftMappingIntervalFamily F x y f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow_hom_ext
  · rw [leftMappingIntervalFamily_source, Category.assoc,
      leftMappingIntervalFamily_source, SSet.comp_const]
  · rw [leftMappingIntervalFamily_target, Category.assoc,
      leftMappingIntervalFamily_target, SSet.comp_const]
  · rw [leftMappingIntervalFamily_h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy_precomp_h,
      leftMappingIntervalFamily_h]
    change (β_ A (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (i ≫ f) =
      (i ▷ Δ[1]) ≫ (β_ B (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl

namespace MappingArrowComparison
variable {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
variable (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison F G)

/-- 概要：比較で写した定値端点の族をホモトピーとして回収する。
方針：比較の端点条件と持ち上げの射影公式を使う。
規約：単位の普遍性は仮定しない。
使われ方：各点の区間写像空間の射の構成。 -/
def intervalHomotopy {A : SSet.{u}} (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    SSet.Homotopy (SSet.const x : A ⟶ X)
      (SSet.const (G.app (Opposite.op ⦋0⦌) y)) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (leftMappingIntervalFamily F x y f ≫ q.map)).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (leftMappingIntervalFamily F x y f ≫ q.map)).h₀,
      Category.assoc, q.source, leftMappingIntervalFamily_source]
    rfl
  h₁ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (leftMappingIntervalFamily F x y f ≫ q.map)).h₁]
    have ht : (leftMappingIntervalFamily F x y f ≫ q.map) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G =
        SSet.const y := by
      rw [Category.assoc, q.target, leftMappingIntervalFamily_target]
    rw [ht, SSet.const_comp]
    rfl
  rel := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (leftMappingIntervalFamily F x y f ≫ q.map)).rel

/-- 概要：各点での比較のホモトピーはパラメータに自然。
方針：持ち上げの自然性と comma の表示の自然性を合成する。
規約：raw な射の等式。
使われ方：各点で定義する単体的な比較の普遍族の公式。 -/
lemma intervalHomotopy_precomp_h {A B : SSet.{u}} (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (i : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    (q.intervalHomotopy x y (i ≫ f)).h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (q.intervalHomotopy x y f).h := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy ((i ≫ leftMappingIntervalFamily F x y f) ≫ q.map)).h :=
      congrArg (fun a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (a ≫ q.map)).h)
        (leftMappingIntervalFamily_precomp F x y i f)
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp i (leftMappingIntervalFamily F x y f ≫ q.map)

/-- 概要：coherent な比較の各点の区間写像空間への制限。
方針：恒等普遍族の像を区間族へ戻す。
規約：同値性を含まない単体集合の射。
使われ方：各点でのホモトピー同値条件を課す対象。 -/
def intervalMap (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (q.intervalHomotopy x y (𝟙 _)))

/-- 概要：各点の比較射は任意の区間族に対して元の比較の作用を表す。
方針：恒等普遍族の回収とパラメータ自然性を合成する。
規約：ホモトピー類を取る前の raw なホモトピーの等式。
使われ方：比較射と構成した単位による標準比較との照合。 -/
lemma intervalMap_family_h {A : SSet.{u}} (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (f ≫ q.intervalMap x y)).h = (q.intervalHomotopy x y f).h := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy_precomp_h]
  have hu : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (q.intervalMap x y)).h =
      (q.intervalHomotopy x y (𝟙 _)).h := by
    unfold intervalMap
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyOfEdge_homotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.simplicialHomotopyOfFunctorEdge_of_homotopy]
  rw [hu]
  simpa only [Category.comp_id] using
    (q.intervalHomotopy_precomp_h x y f (𝟙 _)).symm

/-- 概要：各点の比較射への前合成は、元の族を比較で写して戻す操作と一致。
方針：区間族と関手の辺の全単射および raw な回収公式を使う。
規約：任意の単体集合 A について厳密な等式。
使われ方：同値条件を普遍族だけに課しても全パラメータへ作用することの確認。 -/
lemma intervalMap_family {A : SSet.{u}} (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    f ≫ q.intervalMap x y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (q.intervalHomotopy x y f)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdgeEquiv A X x (G.app (Opposite.op ⦋0⦌) y)).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy _
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyOfEdge_homotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.simplicialHomotopyOfFunctorEdge_of_homotopy]
  apply RelativeMorphism.Homotopy.ext
  exact q.intervalMap_family_h x y f

end MappingArrowComparison
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
