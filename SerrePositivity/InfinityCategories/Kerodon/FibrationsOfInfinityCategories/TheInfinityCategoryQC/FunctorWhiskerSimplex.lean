module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：関手空間の全単体の前後合成の式。
方針：閉構造の合成の二つの単位則を使う。
規約：元の単体と指定射を厳密に保つ。
使われ方：coherent 三単体の指定関手同型の合成則。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：固定関手との前合成は全次数の内部 Hom の作用に等しい。
方針：閉構造の合成の単位則を各次数で評価する。
規約：任意の単体集合と任意の単体を扱う。
使われ方：四面の指定辺を関手同型の前合成にする。 -/
lemma functorPrecomposition_simplex {X Y Z : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (t : ((ihom Y).obj Z) _⦋n⦌) :
    (MonoidalClosed.comp X Y Z).app (Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) n, t) =
      ((pre f).app Z).app (Opposite.op ⦋n⦌) t := by
  have h : (λ_ ((ihom Y).obj Z)).inv ≫ curry' f ▷ ((ihom Y).obj Z) ≫
      MonoidalClosed.comp X Y Z = (pre f).app Z := by
    rw [curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]
  exact congrArg (fun m ↦ m.app (Opposite.op ⦋n⦌) t) h
/-- 概要：固定関手との後合成は全次数の内部 Hom の作用に等しい。
方針：閉構造の合成の単位則を各次数で評価する。
規約：任意の単体集合と任意の単体を扱う。
使われ方：四面の指定辺を関手同型の後合成にする。 -/
lemma functorPostcomposition_simplex {X Y Z : SSet.{u}} (f : Y ⟶ Z) (n : ℕ)
    (t : ((ihom X).obj Y) _⦋n⦌) :
    (MonoidalClosed.comp X Y Z).app (Opposite.op ⦋n⦌)
        (t, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) n) =
      ((ihom X).map f).app (Opposite.op ⦋n⦌) t := by
  have h : (ρ_ ((ihom X).obj Y)).inv ≫ ((ihom X).obj Y) ◁ curry' f ≫
      MonoidalClosed.comp X Y Z = (ihom X).map f := by
    rw [whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]
  exact congrArg (fun m ↦ m.app (Opposite.op ⦋n⦌) t) h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
