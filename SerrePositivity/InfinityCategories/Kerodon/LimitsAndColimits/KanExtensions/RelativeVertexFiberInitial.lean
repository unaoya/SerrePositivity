module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeVertexFiberLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary

/-!
概要：引き戻しへの比較の相対始対象性を指定された頂点 fiber へ制限する。
方針：底を定値とする持ち上げ問題を作り、得た延長を同じ fiber に戻す。
規約：二つの底は異なってよく、充填性は要求しない。
使われ方：相対余錐制限から図式固定の余錐圏の相対普遍性への移行。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：引き戻しへの比較の始点境界充填は対応する二つの fiber の間でも成立する。
方針：標的の境界充填を定値な元の底と組み合わせ、元の比較を充填する。
規約：四つの単体集合に quasicategory 性は不要。
使われ方：全余錐の内部 Hom と図式固定の余錐の族の比較。 -/
lemma kanRelativeVertexFiberMap_initialBoundary {E F B C : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ C) (f : E ⟶ F) (u : B ⟶ C)
    (h : p ≫ u = f ≫ q) (b : B _⦋0⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (pullback.lift p f h) x.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeVertexFiberMap p q f u h b) x := by
  intro n a d hfirst sq
  let t := pullback.lift (f := u) (g := q)
    (SSet.const b : (Δ[n + 1] : SSet.{u}) ⟶ B)
    (d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b)) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.const_comp])
  have sq' : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (boundary (n + 1)).ι
      (pullback.lift p f h) t := by
    constructor
    apply pullback.hom_ext
    · simp only [t, Category.assoc, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
    · simp only [t, Category.assoc, pullback.lift_snd]
      have hs := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b)) sq.w
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeVertexFiberMap_ι] at hs
      exact hs
  have hfirst' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) =
      SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, hfirst, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨l, hl, hlt⟩ := hx n _ _ hfirst' sq'
  have hlp : l ≫ p = SSet.const b := by
    have hs := congrArg (fun z ↦ z ≫ pullback.fst u q) hlt
    simpa only [t, Category.assoc, pullback.lift_fst] using hs
  have hlf : l ≫ f = d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b) := by
    have hs := congrArg (fun z ↦ z ≫ pullback.snd u q) hlt
    simpa only [t, Category.assoc, pullback.lift_snd] using hs
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b l hlp, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hl
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q (u.app (Opposite.op ⦋0⦌) b)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeVertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hlf

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
