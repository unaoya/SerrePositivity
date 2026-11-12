module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderJointEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor

/-!
概要：join の頂点側と図式側を同時に固定する単射。
方針：二因子の coproduct の各単体を場合分けする。
規約：join の内部の混合単体は固定しない。
使われ方：Cat_∞ の極限錐の相対的な輸送。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：join の二因子の和から join への標準射は単射。
方針：同じ因子では包含の単射性、異なる因子では切断位置の違いを使う。
規約：任意の単体集合を扱い、非空性を仮定しない。
使われ方：錐の頂点と図式を同時に指定する制限射。 -/
instance joinSummands_mono (A B : SSet.{u}) :
    Mono (coprod.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (mono_iff_injective _).2
  intro x y h
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sset_coprod_jointly_surjective A B n x <;>
    obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sset_coprod_jointly_surjective A B n y
  · have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app n a = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app n b := by
      simpa only [← NatTrans.comp_app_apply, coprod.inl_desc] using h
    have hab := (mono_iff_injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app n)).mp inferInstance hh
    subst b
    rfl
  · have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app n a = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app n b := by
      simpa only [← NatTrans.comp_app_apply, coprod.inl_desc, coprod.inr_desc] using h
    have he := congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B).obj n ↦ z.1.val) hh
    change n.unop.len + 1 = 0 at he
    omega
  · have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app n a = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app n b := by
      simpa only [← NatTrans.comp_app_apply, coprod.inl_desc, coprod.inr_desc] using h
    have he := congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B).obj n ↦ z.1.val) hh
    change 0 = n.unop.len + 1 at he
    omega
  · have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app n a = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app n b := by
      simpa only [← NatTrans.comp_app_apply, coprod.inr_desc] using h
    have hab := (mono_iff_injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app n)).mp inferInstance hh
    subst b
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
