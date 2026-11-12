module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitTransport

/-!
概要：左右の関手が同時に動く合成の辺を、二つの whisker の合成として読む。
方針：積の対角辺を退化二単体の積で分解し、内部 Hom の固定因子の公式を使う。
規約：元の関手圏の一次・二次単体を保持する。
使われ方：随伴単位条件の全対応空間での不変性と辺の持ち上げ。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：左因子を固定した内部 Hom の合成は元の左関手による前合成。
方針：内部 Hom の全単体の成分で固定関手の作用を計算する。
規約：充填性や随伴性は仮定しない。
使われ方：右関手の比較による単位の変化。 -/
lemma internalHomComposition_fixedLeft {A B Z : SSet.{u}} (L : A ⟶ B) :
    CartesianMonoidalCategory.lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L)) (𝟙 ((ihom B).obj Z)) ≫
      MonoidalClosed.comp A B Z = (pre L).app Z := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex, curry', curry, SSet.unitHomEquiv, SSet.const]
  rfl

/-- 概要：左の比較辺と固定右の積の合成は、右関手による後合成の同じ辺。
方針：固定右の全単体の公式を一次単体で読み、定値辺を恒等辺に同定する。
規約：辺の一次単体の厳密な等式。
使われ方：積の対角辺の第一成分の照合。 -/
lemma internalHomComposition_rightEdge {A B Z : SSet.{u}}
    {L₀ L₁ : A ⟶ B} (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom A).obj B)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₁))
    (R : B ⟶ Z) :
    (((e.tensor (SSet.Truncated.Edge.id
      (X := (truncation 2).obj ((ihom B).obj Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R))).map
      ((truncation 2).map (MonoidalClosed.comp A B Z))).edge) =
    (e.map ((truncation 2).map ((ihom A).map R))).edge := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.internalHomComposition_fixedRight (A := A) R)
  change (MonoidalClosed.comp A B Z).app (Opposite.op ⦋1⦌)
    (e.edge, (SSet.Truncated.Edge.id
      (X := (truncation 2).obj ((ihom B).obj Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R)).edge) = _
  exact (congrArg (fun s ↦ (MonoidalClosed.comp A B Z).app (Opposite.op ⦋1⦌) (e.edge, s))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (X := (ihom B).obj Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R)).symm).trans h

/-- 概要：固定左と右の比較辺の積の合成は、左関手による前合成の同じ辺。
方針：固定左の全単体の公式を一次単体で読み、定値辺を恒等辺に同定する。
規約：辺の一次単体の厳密な等式。
使われ方：積の対角辺の第二成分の照合。 -/
lemma internalHomComposition_leftEdge {A B Z : SSet.{u}} (L : A ⟶ B)
    {R₀ R₁ : B ⟶ Z} (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom B).obj Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R₁)) :
    ((((SSet.Truncated.Edge.id
      (X := (truncation 2).obj ((ihom A).obj B)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L)).tensor e).map
      ((truncation 2).map (MonoidalClosed.comp A B Z))).edge) =
    (e.map ((truncation 2).map ((pre L).app Z))).edge := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge)
    (internalHomComposition_fixedLeft (Z := Z) L)
  change (MonoidalClosed.comp A B Z).app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id
      (X := (truncation 2).obj ((ihom A).obj B)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L)).edge, e.edge) = _
  exact (congrArg (fun s ↦ (MonoidalClosed.comp A B Z).app (Opposite.op ⦋1⦌) (s, e.edge))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (X := (ihom A).obj B) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L)).symm).trans h

/-- 概要：左右の比較辺の対角合成は、後合成と前合成の二つの辺の合成構造を持つ。
方針：左右の退化二単体の積を合成へ写し、両固定因子の辺の公式で正規化する。
規約：元の二単体を使い、新しい充填や整合性を仮定しない。
使われ方：単位の可換三角形と二つの随伴移送の公式の照合。 -/
def internalHomComposition_edgeCompStruct {A B Z : SSet.{u}}
    {L₀ L₁ : A ⟶ B} {R₀ R₁ : B ⟶ Z}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj B))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₁))
    (f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj Z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R₁)) :
    SSet.Truncated.Edge.CompStruct
      (e.map ((truncation 2).map ((ihom A).map R₀)))
      (f.map ((truncation 2).map ((pre L₁).app Z)))
      ((e.tensor f).map ((truncation 2).map (MonoidalClosed.comp A B Z))) := by
  let t := ((SSet.Truncated.Edge.CompStruct.compId e).tensor
    (SSet.Truncated.Edge.CompStruct.idComp f)).map
      ((truncation 2).map (MonoidalClosed.comp A B Z))
  exact ⟨t.simplex, t.d₂.trans (internalHomComposition_rightEdge e R₀),
    t.d₀.trans (internalHomComposition_leftEdge L₁ f), t.d₁⟩

/-- 概要：左右の関手の比較の合成の Hom 類は、二つの whisker の合成。
方針：同じ二単体の合成構造を h Fun に移す。
規約：全関手圏の h の射の等式。
使われ方：対応空間の可逆辺に沿う随伴単位条件の不変性。 -/
lemma internalHomComposition_tensorEdge_hom {A B Z : SSet.{u}}
    {L₀ L₁ : A ⟶ B} {R₀ R₁ : B ⟶ Z}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj B))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₁))
    (f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj Z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R₁)) :
    (hoFunctor.map ((ihom A).map R₀)).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk e) ≫
      (hoFunctor.map ((pre L₁).app Z)).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk f) =
    SSet.Truncated.HomotopyCategory.homMk
      ((e.tensor f).map ((truncation 2).map (MonoidalClosed.comp A B Z))) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (internalHomComposition_edgeCompStruct e f)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
