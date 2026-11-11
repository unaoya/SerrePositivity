module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CosliceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeDiagramReverse
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeRestriction

/-!
概要：密度余錐の添字制限と反対極限錐への反転を照合する。
方針：join の逆反転の自然性で元の全錐の射を計算する。
規約：頂点の正規化と元の添字の全単体を保持する。
使われ方：小さい密度表示から反対 Yoneda の右 Kan 条件への接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：制限した余錐の反転の全射は反転した錐の制限と一致する。
方針：零単体の正規化と join の逆反転の自然性を合成する。
規約：添字と標的の充填性を要求しない。
使われ方：反対密度錐と標準右 Kan 錐の全射の比較。 -/
lemma coconeReverseCone_restrict_val {J K C : SSet.{u}} {D : K ⟶ C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (f : J ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.opFunctor.map f) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (c.restrict f)).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone_val, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone_val]
  change _ = _ ≫ _ ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 _) ≫ c.val)
  rw [CategoryTheory.Functor.map_comp]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableJoinReverse_inv_naturality f (𝟙 (Δ[0] : SSet.{u}))
  simp only [CategoryTheory.Functor.map_id] at h
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 J.op) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u}).op) (SSet.opFunctor.map f) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K Δ[0]).inv) ≫ SSet.opFunctor.map c.val := by
      simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]
    _ = _ := by rw [h]; simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
