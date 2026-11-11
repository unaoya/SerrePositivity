module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceOverColimitCreation
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws

/-!
概要：対象上の小余極限と κ-filtered 余極限を底で作り、射影と後合成の保存を示す。
方針：同じ全余錐に対する射影の検出と元の関手の保存性を使う。
規約：filtered 版には全小余極限の存在・保存を要求しない。
使われ方：accessible・presentable cospan の対象上の表示の同期。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余完備な圏の対象上の圏も全小余極限を持つ。
方針：元の指定余極限を対象上へ持ち上げる。
規約：同じ元の対象を固定する。
使われ方：元の対象上での可算同期。 -/
lemma sliceOver_hasSmallColimits {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x) := by
  intro K a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_hasColimit_of_projection x a (hC K (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x))

/-- 概要：対象上の射影は全小余極限を保存する。
方針：同じ余錐の余極限性を射影で検出する。
規約：元の射影自身の保存性。
使われ方：対象上の列を底の表示へ戻す。 -/
lemma sliceOverProjection_preservesSmallColimits {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) := by
  intro K a c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_iff_projection x (hC K (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)) c).mp hc

/-- 概要：同じ κ-filtered 余極限の存在は対象上の圏へ移る。
方針：指定した filtered 図式の底の余極限だけを使う。
規約：元の圏の全余完備性は不要。
使われ方：accessible cospan の対象上の同期。 -/
lemma sliceOver_hasSmallKappaFilteredColimits {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x) := by
  intro K hK hκ a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_hasColimit_of_projection x a (hC K (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x))

/-- 概要：対象上の射影は指定した κ-filtered 余極限を保存する。
方針：底の同じ形状の余極限性で判定する。
規約：全小余極限の存在を要求しない。
使われ方：accessible 図式の対象上の表示。 -/
lemma sliceOverProjection_isKappaAccessibleFunctor {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) := by
  intro K hK hκ a c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_iff_projection x (hC K (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)) c).mp hc

/-- 概要：余極限保存関手の対象上の後合成も全小余極限を保存する。
方針：像を底の射影で判定し、元の関手の保存性を使う。
規約：全増大余錐を保持する。
使われ方：presentable cospan の対象上の表示の比較。 -/
lemma sliceOverPostcomp_preservesSmallColimits
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (p : C ⟶ D) (hp : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x p) := by
  intro K a c hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_of_projection (x ≫ p)
  have h := hp K (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) c)
    (sliceOverProjection_preservesSmallColimits hC x K a c hc)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
  change (c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (x ≫ p) =
    (c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) ≫ p
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection, Category.assoc]

/-- 概要：κ-filtered 保存関手の対象上の後合成も同じ κ-filtered 余極限を保存する。
方針：同じ余錐を底に射影して元の保存性を使う。
規約：元の全小余極限保存を仮定しない。
使われ方：accessible cospan の対象上での同期。 -/
lemma sliceOverPostcomp_isKappaAccessibleFunctor {κ : Cardinal.{u}}
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C) (p : C ⟶ D)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ p) (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x p) := by
  intro K hK hκ a c hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_of_projection (x ≫ p)
  have h := hp K (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) c)
    (sliceOverProjection_isKappaAccessibleFunctor hC x K a c hc)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
  change (c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (x ≫ p) =
    (c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) ≫ p
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
