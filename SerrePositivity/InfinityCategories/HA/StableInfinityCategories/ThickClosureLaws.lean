module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Thick

/-!
# 共通の厚い閉包と既存の安定閉包の比較

概要：HA §1.1.3・HTT §4.4.5 の厚さを、既存の安定閉包と retract 閉性で照合する。
方針：同じ零・同型・cofiber/fiber の生成手順に沿って帰納する。
規約：retract は元のホモトピー圏で取る。使われ方：厚さの共通の芯への移行。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (C : SSet.{u}) [Quasicategory C] [IsStable C]

/-- 概要：厚い条件は元の安定閉包で閉じる（HA §1.1.3）。
方針：同じ安定閉包の生成手順に沿って帰納する。
規約：指定した実 cofiber/fiber を保つ。使われ方：既存の安定閉性との比較。 -/
lemma IsThick.stableClosure {P : C _⦋0⦌ → Prop} (hP : IsThick C P)
    {x : C _⦋0⦌} (hx : StableVertexClosure {y | P y} x) : P x := by
  induction hx with
  | of_mem h => exact h
  | of_zero h => exact hP.zero h
  | of_iso e _ h => exact hP.iso e h
  | of_cofiber t ht _ _ hx hy => exact hP.cofiber t ht hx hy
  | of_fiber t ht _ _ hy hz => exact hP.fiber t ht hy hz

/-- 概要：元の安定閉性と retract 閉性は共通の厚さに等しい（HA §1.1.3、HTT §4.4.5）。
方針：安定閉包の各生成元に閉性を適用し、逆は帰納原理を使う。
規約：対象集合を商にしない。使われ方：既存の厚い部分圏との共通化。 -/
lemma isThick_iff_stableClosure_retract (P : C _⦋0⦌ → Prop) :
    IsThick C P ↔
      (∀ x, StableVertexClosure {y | P y} x → P x) ∧
      (∀ x y, Nonempty (Retract (HomotopyCategory.mk x) (HomotopyCategory.mk y)) → P y → P x) := by
  constructor
  · intro hP
    exact ⟨fun _ hx => IsThick.stableClosure C hP hx, fun _ _ r hy => hP.retract r hy⟩
  · rintro ⟨hs, hr⟩
    exact {
      zero := fun h => hs _ (.of_zero h)
      iso := fun e hx => hs _ (.of_iso e (.of_mem hx))
      cofiber := fun t ht hx hy => hs _ (.of_cofiber t ht (.of_mem hx) (.of_mem hy))
      fiber := fun t ht hy hz => hs _ (.of_fiber t ht (.of_mem hy) (.of_mem hz))
      retract := fun r hy => hr _ _ r hy }

/-- 概要：既存の安定閉包は同じ厚い閉包に含まれる（HA §1.1.3、HTT §4.4.5）。
方針：元の安定閉包を最小の厚い上界へ送る。
規約：同じ生成条件。使われ方：K の安定閉包との比較。 -/
lemma stableVertexClosure_le_thickClosure (P : C _⦋0⦌ → Prop) {x}
    (hx : StableVertexClosure {y | P y} x) : thickClosure C P x := by
  apply IsThick.stableClosure C (thickClosure_isThick C P)
  induction hx with
  | of_mem h => exact .of_mem (subset_thickClosure C P h)
  | of_zero h => exact .of_zero h
  | of_iso e _ h => exact .of_iso e h
  | of_cofiber t ht _ _ hx hy => exact .of_cofiber t ht hx hy
  | of_fiber t ht _ _ hy hz => exact .of_fiber t ht hy hz

/-- 概要：厚い条件の厚い閉包は元の条件（HA §1.1.3、HTT §4.4.5）。
方針：最小性と生成元の所属を往復する。
規約：頂点条件の等式。使われ方：共通の閉包の冪等則。 -/
lemma thickClosure_eq_self (P : C _⦋0⦌ → Prop) (hP : IsThick C P) :
    thickClosure C P = P := by
  funext x
  exact propext ⟨fun hx => hx P hP (fun _ h => h), subset_thickClosure C P⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
