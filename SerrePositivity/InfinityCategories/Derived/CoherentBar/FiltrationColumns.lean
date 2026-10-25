module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.HomFiltration
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneracyOperators
/-!
概要：元の theta は単体次数を下げ、退化ホモトピーの各列は一段だけ上げる。
方針：元の有限列の各包含先の次元を数え、Hom の標的フィルトレーションへ送る。
規約：元の高次 prefix 項を全て含める。単体次数と cochain 次数を区別する。
使われ方：有限段階の正規化作用素の支持上限と安定化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

private lemma units_mem {V : Type*} [AddCommGroup V] [Module R V]
    (S : Submodule R V) (c : ℤˣ) {z : V} (hz : z ∈ S) : c • z ∈ S :=
  S.toAddSubgroup.zsmul_mem hz c.val

set_option maxHeartbeats 800000 in
-- 元の二種類の有限列の全 Hom end を同時に標的フィルトレーションへ送る。
lemma dgCoherentBarColumn_succ_mem_filtration {n : ℕ} (s : I _⦋n + 1⦌) :
    dgCoherentBarColumn R D F ⟨n + 1, s⟩ ∈
      dgCoherentBarHomFiltration R D F (dgCoherentBarFamily R D F ⟨n + 1, s⟩) 1 n := by
  unfold dgCoherentBarColumn
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro i _
    apply units_mem R
    exact dgCoherentBarHomFiltration_inclusion R D F
      (dgCoherentBarFamily R D F ⟨n + 1, s⟩) 1 n
      (dgCoherentBarFace s i.succ) (by simp [dgCoherentBarFace])
      (dgCoherentBarFaceBlock R D F s i)
  · apply units_mem R
    apply Submodule.sum_mem
    intro k _
    exact dgCoherentBarHomFiltration_inclusion R D F
      (dgCoherentBarFamily R D F ⟨n + 1, s⟩) 1 n
      (dgCoherentBarTail s (k.val + 1) (by omega)) (by
        dsimp [dgCoherentBarTail]
        omega)
      (dgCoherentBarPrefixBlock R D F s k.val (by omega))

set_option maxHeartbeats 800000 in
-- 一般の次元ラベルを元の有限列の Hom end に照合するための局所上限。
lemma dgCoherentBarColumn_mem_filtration (s : dgCoherentBarIndex I) :
    dgCoherentBarColumn R D F s ∈
      dgCoherentBarHomFiltration R D F (dgCoherentBarFamily R D F s) 1 (s.1 - 1) := by
  rcases s with ⟨n, s⟩
  cases n with
  | zero => exact Submodule.zero_mem _
  | succ n =>
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
      (dgCoherentBarColumn_succ_mem_filtration R D F s)

lemma dgCoherentBarDegeneracyColumn_mem_filtration {n : ℕ} (s : I _⦋n⦌)
    (i : Fin (n + 1)) :
    dgCoherentBarDegeneracyColumn R D F s i ∈
      dgCoherentBarHomFiltration R D F (dgCoherentBarFamily R D F ⟨n, s⟩) (-1) (n + 1) :=
  dgCoherentBarHomFiltration_inclusion R D F (dgCoherentBarFamily R D F ⟨n, s⟩) (-1) (n + 1)
    (dgCoherentBarDegeneracy s i) le_rfl (dgCoherentBarDegeneracyBlock R D F s i)

set_option maxHeartbeats 800000 in
-- 同じ退化ブロックの全 Hom と標的次数上限の照合に限った局所上限。
lemma dgCoherentBarNormalizationHomotopyColumn_mem_filtration (q : ℕ)
    (s : dgCoherentBarIndex I) :
    dgCoherentBarNormalizationHomotopyColumn R D F q s ∈
      dgCoherentBarHomFiltration R D F (dgCoherentBarFamily R D F s) (-1) (s.1 + 1) := by
  rcases s with ⟨n, s⟩
  unfold dgCoherentBarNormalizationHomotopyColumn
  split_ifs
  · exact Submodule.zero_mem _
  · exact units_mem R _ _ (dgCoherentBarDegeneracyColumn_mem_filtration R D F s _)

end SerrePositivity.InfinityCategories
