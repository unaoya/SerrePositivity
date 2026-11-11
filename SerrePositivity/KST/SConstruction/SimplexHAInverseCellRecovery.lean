module
public import SerrePositivity.KST.SConstruction.SimplexHAInverseCellRecoveryCondition

/-! # 元の全ての HA 部分集合 cell の実像回収
概要：元の任意の昇順列と終点の部分集合 cell の像は、同じ元の HA 実鎖射。
方針：全区間を基底とし、欠落頂点数の強い帰納で一頂点を補い、同じ零面で削除する。
規約：元の全頂点・実 cell・全次数を保持。使われ方：native HA 復元のもう一方の逆律。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の任意の部分集合 cell の逆 dg 関手による像は、同じ元の HA 鎖射を回収する。 -/
lemma simplexHAInverseCellRecovery {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b) :
    SimplexHAInverseCellRecovery A s m v b hb := by
  have all (k : ℕ) : ∀ (m : ℕ) (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1))
      (hb : v (Fin.last m) < b),
      (Finset.Icc (v 0) b \ simplexHADecodeSubset m v {b}).card = k →
        SimplexHAInverseCellRecovery A s m v b hb := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m v b hb hk
      let I := simplexHADecodeSubset m v {b}
      let J := Finset.Icc (v 0) b
      have hIJ : I ⊆ J := by
        intro x hx
        rcases (simplexHADecodeSubset_mem m v {b} x).mp hx with ⟨i, rfl⟩ | hx
        · exact Finset.mem_Icc.mpr ⟨v.monotone (Fin.zero_le i),
            ((v.monotone (Fin.le_last i)).trans_lt hb).le⟩
        · obtain rfl := Finset.mem_singleton.mp hx
          exact Finset.mem_Icc.mpr ⟨((v.monotone (Fin.zero_le _)).trans_lt hb).le, le_rfl⟩
      by_cases hfull : I = J
      · exact simplexHAInverseCellRecovery_of_full A s v b hb hfull
      · have hmissing : (J \ I).Nonempty := Finset.sdiff_nonempty.mpr
          (fun hJI => hfull (hIJ.antisymm hJI))
        obtain ⟨j, hj⟩ := hmissing
        obtain ⟨hjJ, hjI⟩ := Finset.mem_sdiff.mp hj
        have hstart : v 0 ∈ I :=
          (simplexHADecodeSubset_mem m v {b} _).mpr (Or.inl ⟨0, rfl⟩)
        have hend : b ∈ I :=
          (simplexHADecodeSubset_mem m v {b} _).mpr (Or.inr (Finset.mem_singleton_self b))
        have hfirst : v 0 < j := lt_of_le_of_ne (Finset.mem_Icc.mp hjJ).1
          (fun he => hjI (he ▸ hstart))
        have hjb : j < b := lt_of_le_of_ne (Finset.mem_Icc.mp hjJ).2
          (fun he => hjI (he.symm ▸ hend))
        have hjv : j ∉ Finset.univ.map v.toEmbedding :=
          fun h => hjI (Finset.mem_union_left _ h)
        let w := simplexHAInsertVertexOrder v j hjv
        have hw := simplexHAInsertVertexOrder_last_lt v j hjv b hb hjb
        have hfirst' := simplexHAInsertVertexOrder_first v j hjv hfirst
        have hset : simplexHADecodeSubset (m + 1) w {b} = insert j I := by
          change (Finset.univ.map w.toEmbedding) ∪ {b} =
            insert j ((Finset.univ.map v.toEmbedding) ∪ {b})
          rw [simplexHAInsertVertexOrder_vertices, Finset.insert_union]
        have hlt : (Finset.Icc (w 0) b \ simplexHADecodeSubset (m + 1) w {b}).card < k := by
          rw [hfirst', hset, Finset.sdiff_insert]
          exact (Finset.card_erase_lt_of_mem hj).trans_eq hk
        exact simplexHAInverseCellRecovery_insert A s v b hb j hjv hfirst hjb
          (ih _ hlt (m + 1) w b hw rfl)
  exact all _ m v b hb rfl

end SerrePositivity.KST.SConstruction
