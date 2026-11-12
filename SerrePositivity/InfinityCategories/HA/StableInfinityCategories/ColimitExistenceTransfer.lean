module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRestriction

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachment
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-! # 余錐の厳密な延長と余極限の存在の転送

概要：coslice の制限が trivial Kan fibration なら、指定した余錐とその余極限性を全体へ延長できる。
方針：制限射の厳密な切断で余錐を持ち上げ、始対象性の保存・反映を使う。
規約：部分図式上の余錐を等号で保持する。使われ方：懸垂の付加による有限余極限の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：right anodyne な部分図式の余極限を全体へ厳密に延長できる。
方針：coslice 制限の trivial Kan fibration 性を適用する。
規約：余錐全体と頂点を保持する。使われ方：標準 span から補助図式への転送。 -/
lemma exists_colimitCocone_extension_of_rightAnodyne {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (f : L ⟶ K) [Mono f] (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions f)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ p)) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ c.restrict f = d ∧ c.vertex = d.vertex := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration p f hf
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCocone_extension_of_trivialRestriction p f d hd

/-- 概要：余極限余錐を付加した図式の余極限を残る図式から厳密に延長できる。
方針：余極限付加による coslice 制限の trivial Kan fibration 性を使う。
規約：付加する図式の射には単射性を要求しない。使われ方：懸垂からの直和の構成。 -/
lemma exists_colimitCocone_extension_of_colimit_attachment
    {K C D X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : K ⟶ C)
    (j : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] ⟶ D) (k : C ⟶ D) (hp : IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) i j k)
    (F : D ⟶ X) (hj : j ≫ F = c.val)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (k ≫ F)) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone e ∧ e.restrict k = d ∧ e.vertex = d.vertex := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceRestriction_trivialKanFibration_of_colimit_attachment c hc i j k hp F hj
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCocone_extension_of_trivialRestriction F k d hd

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
