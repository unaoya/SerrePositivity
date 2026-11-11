module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoPastingEndpointTransport

/-!
概要：指定された局所自然性の三辺の等式を、同じ同型の二辺の貼り合わせへまとめる。
方針：圏の対象で型付けした同型の合成・結合則・指定値の一致を使う。
規約：元の同型と元の三辺の等式を保持する。
使われ方：関手の射を逆算せず、既存の局所自然性の三角等式を回収する。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 二つの指定同型の合成は、直接の指定同型に一致する。 -/
def IsoTriangleCommutes {C : Type u} [Category.{v} C] {a b t : C}
    (V : a ≅ b) (K : b ≅ t) (D : a ≅ t) : Prop := V ≪≫ K = D

/-- 指定局所比較の二因子に元の大域自然性を貼ると、直接の大域自然性になる。 -/
def IsoLocalTriangleCommutes {C : Type u} [Category.{v} C] {a b c t : C}
    (V : a ≅ b) (W : b ≅ c) (K : c ≅ t) (D : a ≅ t) : Prop := V ≪≫ W ≪≫ K = D

/-- 同じ指定値の第二因子への表示変更は、三辺の等式を保持する。 -/
lemma IsoLocalTriangleCommutes.replace_second {C : Type u} [Category.{v} C]
    {a b c t : C} {V : a ≅ b} {W : b ≅ c} {K : c ≅ t} {D : a ≅ t}
    (h : IsoLocalTriangleCommutes V W K D) (W' : b ≅ c) (hw : HEq W' W) :
    IsoLocalTriangleCommutes V W' K D := by
  cases eq_of_heq hw
  exact h

/-- 同じ指定二因子をまとめても、元の大域自然性に対する三角等式を保持する。 -/
lemma IsoLocalTriangleCommutes.merge {C : Type u} [Category.{v} C]
    {a b c t : C} {V : a ≅ b} {W : b ≅ c} {K : c ≅ t} {D : a ≅ t}
    (h : IsoLocalTriangleCommutes V W K D) : IsoTriangleCommutes (V ≪≫ W) K D := by
  unfold IsoTriangleCommutes
  unfold IsoLocalTriangleCommutes at h
  simpa only [Iso.trans_assoc] using h

/-- 同じ指定値の第一辺への表示変更は、三角等式を保持する。 -/
lemma IsoTriangleCommutes.replace_first {C : Type u} [Category.{v} C]
    {a b t : C} {V : a ≅ b} {K : b ≅ t} {D : a ≅ t}
    (h : IsoTriangleCommutes V K D) (V' : a ≅ b) (hV : HEq V' V) :
    IsoTriangleCommutes V' K D := by
  cases eq_of_heq hV
  exact h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
