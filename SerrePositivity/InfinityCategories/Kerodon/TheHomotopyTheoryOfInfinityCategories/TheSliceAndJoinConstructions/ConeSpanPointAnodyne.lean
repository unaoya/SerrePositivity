module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSpanShape

/-!
概要：二つの右余錐の貼り合わせへ入る指定三頂点 span は right anodyne。
方針：第一の辺を右余錐へ拡大し、第二の余錐の相対境界を付着する。
規約：共通部分への指定点は right anodyne、第二の共通部分包含は単射。
使われ方：形状の pushout に対する余極限の存在の貼り合わせ。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 同じ始点を持つ二つの辺を貼った三頂点 span の形状。 -/
def pointConeSpan : SSet.{u} :=
  pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] :
    SSet.{u}))

variable {A B C : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ A) (i : A ⟶ B) (j : A ⟶ C)

/-- 第一の辺を第一の右余錐全体に拡大する。 -/
def coneSpanPointExpansion : pointConeSpan.{u} ⟶
    pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) (a ≫ (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B (Δ[0] : SSet.{u}))) :=
  pushout.desc (pushout.inl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (a ≫ i) (𝟙 (Δ[0] : SSet.{u})) ≫ pushout.inr _ _) (by
    calc
      _ = (a ≫ (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B (Δ[0] : SSet.{u}))) ≫ pushout.inr _ _ := pushout.condition
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (a ≫ i) (𝟙 (Δ[0] :
        SSet.{u}))) ≫ pushout.inr _ _ :=
        congrArg (fun z : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B (Δ[0] : SSet.{u}) => z ≫ pushout.inr _ _)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanPoint_boundary a i).symm
      _ = _ := Category.assoc _ _ _)

/-- 第一の辺の拡大は right anodyne。 -/
lemma coneSpanPointExpansion_rightAnodyne :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (coneSpanPointExpansion a i) := by
  have : Mono (a ≫ i) := by
    rw [NatTrans.mono_iff_mono_app]
    rintro ⟨⟨n⟩⟩
    rw [mono_iff_injective]
    intro x y _
    apply stdSimplex.ext
    intro k
    apply Fin.ext
    have hx := (x k).isLt
    have hy := (y k).isLt
    omega
  have ho : IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (a ≫ i) (𝟙 (Δ[0] : SSet.{u})))
      (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u})
        (Δ[0] : SSet.{u})) ≫
        coneSpanPointExpansion a i)
      (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) (a ≫ (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B (Δ[0] :
        SSet.{u})))) := by
    simpa only [coneSpanPointExpansion, pushout.inl_desc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp, Category.assoc] using
      (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) (a ≫ (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl
        B (Δ[0] : SSet.{u}))))
  have hs := ho.of_top (show
      pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u})
        (Δ[0] : SSet.{u})) ≫
        coneSpanPointExpansion a i =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (a ≫ i) (𝟙 (Δ[0] : SSet.{u})) ≫ _ from ?_)
      (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] :
        SSet.{u}) (Δ[0] : SSet.{u})))
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.of_isPushout hs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPoint_mono_rightAnodyne (a ≫ i))
  · exact pushout.inr_desc _ _ _

/-- 三頂点 span の指定写像。 -/
def coneSpanPointMap : pointConeSpan.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanShape i j :=
  coneSpanPointExpansion a i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanPointCompletion a i j

/-- 指定点が共終なら、同じ三頂点 span の包含も right anodyne。 -/
lemma coneSpanPointMap_rightAnodyne [Mono a] [Mono j]
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions a) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (coneSpanPointMap a i j) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.comp_mem _ _ (coneSpanPointExpansion_rightAnodyne a i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanPointCompletion_rightAnodyne a i j ha)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
