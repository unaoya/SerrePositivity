module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FullCosliceLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

/-!
概要：全部分包含は、元の同じ余錐の native な余極限性を反映する。
方針：周囲の coslice 内の始対象の境界充填を、全頂点の条件で元の全部分 coslice へ戻す。
規約：充満忠実性や余極限性を追加の instance 仮定にしない。
使われ方：Ind の前層内の余極限から、同じ Ind 内の余極限を得る。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 全部分包含で写した同じ余錐が余極限なら、元の余錐も余極限。 -/
lemma isColimitCone_of_fullInclusion {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    {D : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (q.app (Opposite.op ⦋0⦌) c) := hc
  intro n b hb
  have hqb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (b ≫ q) =
      SSet.yonedaEquiv.symm (q.app (Opposite.op ⦋0⦌) c) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hi n (b ≫ q) hqb
  have hv : ∀ v, P ((F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      (D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)).app (Opposite.op ⦋0⦌) v) := by
    intro v
    have hvb : v ∈ (boundary (n + 1)).obj (Opposite.op ⦋0⦌) := by
      have hz : stdSimplex.obj₀Equiv.symm (stdSimplex.obj₀Equiv v) = v :=
        Equiv.symm_apply_apply _ v
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n (stdSimplex.obj₀Equiv v)
      rw [hz] at h
      exact h
    let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, hvb⟩
    have he : F.app (Opposite.op ⦋0⦌) v = (b ≫ q).app (Opposite.op ⦋0⦌) w :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hF (Opposite.op ⦋0⦌)) w
    change P ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection _).app (Opposite.op ⦋0⦌)
      (F.app (Opposite.op ⦋0⦌) v))
    rw [he]
    change P (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)).app (Opposite.op ⦋0⦌))
        (b.app (Opposite.op ⦋0⦌) w))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection D).app (Opposite.op ⦋0⦌) (b.app (Opposite.op ⦋0⦌) w))
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCosliceLift P D F hv
  refine ⟨L, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCoslicePostcomp_cancel P D
  change (boundary (n + 1)).ι ≫ (L ≫ q) = b ≫ q
  rw [show L ≫ q = F from _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCosliceLift_postcomp P D F hv, hF]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
