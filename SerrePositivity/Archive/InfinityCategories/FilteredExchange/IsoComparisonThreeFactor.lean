module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
概要：比較の自然性と三因子の整合式を合成する。
方針：同型の結合則と関手による像だけを使う。
規約：元の全因子を保持。使われ方：左右 Hom の値の指定比較の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 比較の自然性に同じ三因子の整合を合成しても指定された因子を保持する。 -/
lemma iso_comparison_compose_three {C : Type u} [Category.{v} C]
    {a b c d e f : C} (A : a ≅ b) (i : a ≅ c) (j : b ≅ d)
    (L : c ≅ d) (S : d ≅ e) (R : e ≅ f) (T : c ≅ f)
    (hA : A ≪≫ j = i ≪≫ L) (hL : L ≪≫ S ≪≫ R = T) :
    A ≪≫ j ≪≫ S ≪≫ R = i ≪≫ T := by
  calc
    _ = (A ≪≫ j) ≪≫ S ≪≫ R := by simp only [Iso.trans_assoc]
    _ = (i ≪≫ L) ≪≫ S ≪≫ R := by rw [hA]
    _ = _ := by simpa only [Iso.trans_assoc] using congrArg (fun t => i ≪≫ t) hL

/-- 同じ三因子の整合式を一つの単体集合の射で写す。 -/
lemma vertexIso_map_three_factor {X Y : SSet.{u}} {a b c d : X _⦋0⦌}
    (L : VertexIso a b) (S : VertexIso b c) (R : VertexIso c d) (T : VertexIso a d)
    (m : X ⟶ Y) (h : L ≪≫ S ≪≫ R = T) :
    VertexIso.map L m ≪≫ VertexIso.map S m ≪≫ VertexIso.map R m = VertexIso.map T m := by
  simpa only [VertexIso.map, CategoryTheory.Functor.mapIso_trans] using
    congrArg (fun t => VertexIso.map t m) h

end SerrePositivity.InfinityCategories.F2
