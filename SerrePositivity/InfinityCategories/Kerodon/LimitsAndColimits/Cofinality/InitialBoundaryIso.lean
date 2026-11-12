module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary

/-!
概要：相対始点境界充填を始域と標的の可換な同型で移送する。
方針：境界持ち上げ問題を逆同型で戻し、充填を順同型で送る。
規約：quasicategory 性やファイブレーション性は不要。
使われ方：Kan 拡張の関手の族の fiber と通常の余錐制限の比較。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：相対始点境界充填は始域と標的の可換な同型で保たれる。
方針：逆同型で持ち上げ問題を戻し、充填を順同型で写す。
規約：同型の平方は厳密に可換。
使われ方：fiber ごとの普遍余錐の充填条件の移送。 -/
lemma InitialBoundaryLifting.map_iso {E B E' B' : SSet.{u}}
    {p : E ⟶ B} {q : E' ⟶ B'} (e : E ≅ E') (d : B ≅ B')
    (h : e.hom ≫ q = p ≫ d.hom) {x : E _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting q (e.hom.app (Opposite.op ⦋0⦌) x) := by
  have hi : e.inv ≫ p = q ≫ d.inv := by
    apply (cancel_mono d.hom).1
    rw [Category.assoc, ← h, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  intro n a b ha sq
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (a ≫ e.inv) = SSet.yonedaEquiv.symm x := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
    have he : e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) x) = x := by
      change (e.hom ≫ e.inv).app (Opposite.op ⦋0⦌) x = x
      rw [Iso.hom_inv_id]
      rfl
    rw [he]
  have sq' : CommSq (a ≫ e.inv) (boundary (n + 1)).ι p (b ≫ d.inv) := by
    constructor
    rw [Category.assoc, hi, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨F, hF, hFp⟩ := hx n _ _ hfirst sq'
  refine ⟨F ≫ e.hom, ?_, ?_⟩
  · rw [← Category.assoc, hF, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, h, ← Category.assoc, hFp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialBoundaryLifting (map_iso)


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
