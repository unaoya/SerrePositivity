module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-!
概要：二入力の指定全円柱を、区間境界上の全円柱へまとめる。
方針：時間をパラメータへ移し、元の二端点の境界図式を使う。
規約：元の二円柱を全時刻で厳密に保持する。
使われ方：元の部分 path 正方形との相対境界での貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {A X : SSet.{u}} {f₀ f₁ g₀ g₁ : A ⟶ X}
  (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy g₀ g₁)

/-- 概要：二端点の全輸送を区間境界上で同時に記録するホモトピー。
方針：元の二つの円柱を境界図式にする。
規約：時間は右。使われ方：相対 path 境界の両端の円柱。 -/
def intervalBoundaryHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f₀ g₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f₁ g₁) where
  h := (α_ (boundary 1 : SSet.{u}) A (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram U.h V.h
  h₀ := by
    change ((boundary 1 : SSet.{u}) ◁ SSet.ι₀) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram U.h V.h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f₀ g₀
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, U.h₀, V.h₀]
  h₁ := by
    change ((boundary 1 : SSet.{u}) ◁ SSet.ι₁) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram U.h V.h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f₁ g₁
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, U.h₁, V.h₁]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：区間境界の始点上の全円柱は元の第一円柱。
方針：境界図式の始点を評価。規約：全時刻。使われ方：共通部分の第一端の照合。 -/
lemma intervalBoundaryHomotopy_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A ▷ (Δ[1] : SSet.{u})) ≫
      (intervalBoundaryHomotopy U V).h = U.h := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 (A ⊗ (Δ[1] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram U.h V.h = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero _ _

/-- 概要：区間境界の終点上の全円柱は元の第二円柱。
方針：境界図式の終点を評価。規約：全時刻。使われ方：共通部分の第二端の照合。 -/
lemma intervalBoundaryHomotopy_one :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫
      (intervalBoundaryHomotopy U V).h = V.h := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 (A ⊗ (Δ[1] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram U.h V.h = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
