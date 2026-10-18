module

public import Mathlib.Data.Finset.Lattice.Fold

/-!
# 有限交叉の局所条件から有限和への帰納

概要：二項の和と交叉の貼り合わせを、有限族の全ての非空な交叉の条件から適用する。
方針：新しい要素との交叉の族へ、同じ有限集合の帰納仮定を使う。
規約：Segal 1974 Proposition 1.6 の標準単体の境界の有限被覆に使う束論的な補助。
使われ方：各面とその交叉から境界全体のホモトピー引き戻しへ進む。
-/

@[expose] public section
namespace SerrePositivity.KST.Comparison

/--
概要：有限族の全ての非空な部分族の交叉の条件から、全体の和の条件を得る。
方針：二項の貼り合わせと分配則で、新しい要素との交叉の族にも帰納を適用する。
規約：性質の二項の貼り合わせと空対象の条件を明示する一般的な束の補題。
使われ方：標準単体の境界の有限被覆の帰納。
-/
theorem finiteSup_of_nonempty_intersections
    {L : Type*} [DistribLattice L] [OrderBot L] [OrderTop L]
    (P : L → Prop) (hbot : P ⊥)
    (hglue : ∀ a b, P a → P b → P (a ⊓ b) → P (a ⊔ b))
    {ι : Type*} (s : Finset ι) (U : ι → L)
    (hlocal : ∀ t : Finset ι, t ⊆ s → t.Nonempty → P (t.inf U)) : P (s.sup U) := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty => simpa using hbot
  | @insert i s hi ih =>
    have hs : P (s.sup U) := ih U (fun t ht hne =>
      hlocal t (ht.trans (Finset.subset_insert i s)) hne)
    have hiP : P (U i) := by
      have h := hlocal {i} (by simp) (by simp)
      simpa using h
    have hI : P (s.sup (fun j => U i ⊓ U j)) := by
      apply ih
      intro t ht hne
      have h := hlocal (insert i t) (Finset.insert_subset_insert i ht) (by simp)
      rw [Finset.inf_insert] at h
      have heq : t.inf (fun j => U i ⊓ U j) = U i ⊓ t.inf U := by
        calc
          _ = t.inf (fun _ => U i) ⊓ t.inf U :=
            Finset.inf_inf (s := t) (f := fun _ => U i) (g := U)
          _ = _ := by rw [Finset.inf_const hne]
      exact heq.symm ▸ h
    rw [Finset.sup_insert]
    apply hglue (U i) (s.sup U) hiP hs
    rw [Finset.sup_inf_distrib_left]
    exact hI

end SerrePositivity.KST.Comparison
