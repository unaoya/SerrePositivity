module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalExtension

/-!
概要：相対終点境界充填の可換な同型による移送。
方針：境界と標的の単体を逆同型で戻して充填する。
規約：始域・標的の両方の同型を扱う。
使われ方：Kerodon §7.1.6（Tag 02KF）・7.1.8（Tag 02X8） の二重内部 Hom の交換。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：相対終点境界充填は始域と標的の可換な同型で保たれる。
方針：逆同型で持ち上げ問題を戻し、充填を順同型で写す。
規約：quasicategory 性やファイブレーション性は不要。
使われ方：Kerodon §7.1.8（Tag 02X8） の関手圏の二変数の交換。 -/
lemma TerminalBoundaryLifting.map_iso {E B E' B' : SSet.{u}}
    {p : E ⟶ B} {q : E' ⟶ B'} (e : E ≅ E') (d : B ≅ B')
    (h : e.hom ≫ q = p ≫ d.hom) {x : E _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting q (e.hom.app (Opposite.op ⦋0⦌) x) := by
  have hi : e.inv ≫ p = q ≫ d.inv := by
    apply (cancel_mono d.hom).1
    rw [Category.assoc, ← h, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  intro n a b ha sq
  have hend : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (a ≫ e.inv) =
      SSet.yonedaEquiv.symm x := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
    have he : e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) x) = x := by
      change (e.hom ≫ e.inv).app (Opposite.op ⦋0⦌) x = x
      rw [Iso.hom_inv_id]
      rfl
    rw [he]
  have sq' : CommSq (a ≫ e.inv) (boundary (n + 1)).ι p (b ≫ d.inv) := by
    constructor
    rw [Category.assoc, hi, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨F, hF, hFp⟩ := hx n _ _ hend sq'
  refine ⟨F ≫ e.hom, ?_, ?_⟩
  · rw [← Category.assoc, hF, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, h, ← Category.assoc, hFp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
