module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
概要：全関手同型と元の明示的な同値が、各指定点の成分に与える一致。
方針：同じ全ホモトピーを指定点へ評価する。
規約：元の写像・点を保持。使われ方：余錐脚の全比較の成分への移送。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 全関手同型は、元の任意の指定点の像の成分を一致させる。 -/
lemma functorIso_point_component {A X : SSet.{u}} [Quasicategory X]
    {f g : A ⟶ X} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (a : A _⦋0⦌) :
    SSet.π₀.mk (f.app (Opposite.op ⦋0⦌) a) =
      SSet.π₀.mk (g.app (Opposite.op ⦋0⦌) a) :=
  SSet.π₀.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge h.simplicialHomotopy a)

/-- 選択済みの逆から順方向へ戻すと、元の同じ点の成分を回収する。 -/
lemma qCatEquivalence_inv_hom_component {A X : SSet.{u}} [Quasicategory A] [Quasicategory X]
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A X) (x : X _⦋0⦌) :
    SSet.π₀.mk (q.hom.app (Opposite.op ⦋0⦌) (q.inv.app (Opposite.op ⦋0⦌) x)) =
      SSet.π₀.mk x :=
  functorIso_point_component q.invHomIso x

/-- 全比較を持つ値写像は、元の fiber 側の成分回収を値側の同じ射へ移す。 -/
lemma componentRepresentative_of_valueIso {J : Type u} {Z Y : SSet.{u}}
    [Quasicategory Z] [Quasicategory Y] (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Z Y)
    (W X : J → SSet.{u}) (a : ∀ j, W j ⟶ X j)
    (f : ∀ j, W j ⟶ Z) (g : ∀ j, X j ⟶ Y)
    (h : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f j ≫ q.hom) (a j ≫ g j))
    (hs : ∀ z : Z _⦋0⦌, ∃ j, ∃ w : W j _⦋0⦌,
      SSet.π₀.mk ((f j).app (Opposite.op ⦋0⦌) w) = SSet.π₀.mk z)
    (y : Y _⦋0⦌) :
    ∃ j, ∃ x : X j _⦋0⦌,
      SSet.π₀.mk ((g j).app (Opposite.op ⦋0⦌) x) = SSet.π₀.mk y := by
  obtain ⟨j, w, hw⟩ := hs (q.inv.app (Opposite.op ⦋0⦌) y)
  have hh := functorIso_point_component (h j) w
  change SSet.π₀.mk (q.hom.app (Opposite.op ⦋0⦌)
      ((f j).app (Opposite.op ⦋0⦌) w)) =
    SSet.π₀.mk ((g j).app (Opposite.op ⦋0⦌) ((a j).app (Opposite.op ⦋0⦌) w)) at hh
  have hq := congrArg (SSet.mapπ₀ q.hom) hw
  simp only [SSet.mapπ₀_mk] at hq
  exact ⟨j, (a j).app (Opposite.op ⦋0⦌) w,
    hh.symm.trans (hq.trans (qCatEquivalence_inv_hom_component q y))⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
