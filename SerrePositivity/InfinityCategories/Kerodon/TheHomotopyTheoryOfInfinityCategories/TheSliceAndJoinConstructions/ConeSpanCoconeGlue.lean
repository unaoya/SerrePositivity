module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSpanColimitTransfer

/-!
概要：共有部分で一致する二つの全余錐を、右余錐の貼り合わせ上で接続する。
方針：全余錐の射を pushout の普遍性で貼り、元の余極限性を回収する。
規約：両余錐の全単体を厳密に保持する。
使われ方：共通の部分余極限を付加した二つの図式から全体の図式を作る。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
/-- 同じ全余錐の射に対する余極限性は、底の表示に依存しない。 -/
lemma isColimitCone_iff_of_sameMap {J X : SSet.{u}} {p q : J ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (h : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := by
  have hp : p = q := c.property.symm.trans
    ((congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ k) h).trans d.property)
  subst q
  have hc : c = d := Subtype.ext h
  rw [hc]

variable {A B C X : SSet.{u}} (i : A ⟶ B) (j : A ⟶ C)
  {p : B ⟶ X} {q : C ⟶ X} (b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q)
  (h : i ≫ p = j ≫ q)

/-- 共通部分上で一致する全余錐を厳密に貼った図式。 -/
def coneSpanCoconeGlue : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanShape i j ⟶ X :=
  pushout.desc b.val c.val (by
    simpa only [Category.assoc, b.property, c.property] using h)

/-- 元の左余錐の全単体の回収。 -/
lemma coneSpanCoconeGlue_left :
    pushout.inl (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0]) (j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl C Δ[0]) ≫
      coneSpanCoconeGlue i j b c h = b.val := pushout.inl_desc _ _ _

/-- 元の右余錐の全単体の回収。 -/
lemma coneSpanCoconeGlue_right :
    pushout.inr (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0]) (j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl C Δ[0]) ≫
      coneSpanCoconeGlue i j b c h = c.val := pushout.inr_desc _ _ _

/-- 貼った図式の左側は、指定された余極限余錐そのものである。 -/
lemma coneSpanCoconeGlue_left_isColimit (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanLeftCocone i j (coneSpanCoconeGlue i j b c h)) := by
  exact (isColimitCone_iff_of_sameMap _ b (coneSpanCoconeGlue_left i j b c h)).mpr hb

/-- 貼った図式の右側は、指定された余極限余錐そのものである。 -/
lemma coneSpanCoconeGlue_right_isColimit (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanRightCocone i j (coneSpanCoconeGlue i j b c h)) := by
  exact (isColimitCone_iff_of_sameMap _ c (coneSpanCoconeGlue_right i j b c h)).mpr hc

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
