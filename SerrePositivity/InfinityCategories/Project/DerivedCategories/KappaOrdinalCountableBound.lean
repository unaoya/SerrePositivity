module
public import Mathlib.SetTheory.Cardinal.Regular

/-!
概要：正則非可算 κ の小さい射影的代表族を、実際の加群演算で閉じる。
方針：小さい超限段階と可算個の段階の狭義上界で、同じ代表族の閉性を証明する。
規約：全同型コピーを集めず、全共変 Hom の κ-compact 性は別に証明する。
使われ方：K-7 の実 dg 小模型への対象・小ささ・射影性・直和閉性の供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma kappaOrdinal_countable_strict_bound {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular) (s : ℕ → κ.ord.ToType) :
    ∃ b : κ.ord.ToType, ∀ n, s n < b := by
  let f : ULift.{u} ℕ → Ordinal.{u} := fun n ↦ (s n.down).toOrd.val
  have hcof : Cardinal.mk (ULift.{u} ℕ) < κ.ord.cof := by
    simpa only [hreg.cof_ord, Cardinal.mk_uLift, Cardinal.lift_aleph0,
      Cardinal.mk_nat] using hκ
  have hb : (⨆ n, f n + 1) < κ.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof hcof (fun n ↦ (s n.down).toOrd.property)
  let b : κ.ord.ToType := Ordinal.ToType.mk ⟨⨆ n, f n + 1, hb⟩
  refine ⟨b, fun n ↦ ?_⟩
  have hn : (s n).toOrd.val < ⨆ i, f i + 1 :=
    lt_of_lt_of_le (lt_add_one _) (Ordinal.le_iSup (fun i ↦ f i + 1) (ULift.up n))
  have ht := (Ordinal.ToType.mk (o := κ.ord)).strictMono
    (show (s n).toOrd < ⟨⨆ i, f i + 1, hb⟩ from hn)
  simpa only [Ordinal.ToType.toOrd, OrderIso.apply_symm_apply] using ht

end SerrePositivity.InfinityCategories.Project.DerivedCategories
