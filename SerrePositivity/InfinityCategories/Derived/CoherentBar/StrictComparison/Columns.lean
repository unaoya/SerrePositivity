module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Diagram

/-!
概要：strict 図式では bar の高次 prefix 項が消え、通常の face 項だけが残る。
方針：dg nerve 包含の高次零成分を shift ブロックまで輸送する。
規約：元の theta と符号を保つ。
使われ方：augmentation の閉性と filtered bar の縮約。
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
  {J : Type u} [Category J] (F : J ⥤ ModuleCategory R D)

lemma dgCoherentBarStrictPrefixHom_eq_zero {n : ℕ} (s : (nerve J) _⦋n⦌)
    (k : ℕ) (hk : 0 < k) (h : k + 1 ≤ n) :
    dgCoherentBarPrefixHom R D (dgCoherentBarStrictDiagram R D F) s k h = 0 := by
  unfold dgCoherentBarPrefixHom
  rw [dgCoherentBarStrictTop_eq_zero R D F hk]
  exact map_zero _

lemma dgCoherentBarStrictPrefixBlock_eq_zero {n : ℕ} (s : (nerve J) _⦋n⦌)
    (k : ℕ) (hk : 0 < k) (h : k + 1 ≤ n) :
    dgCoherentBarPrefixBlock R D (dgCoherentBarStrictDiagram R D F) s k h = 0 := by
  unfold dgCoherentBarPrefixBlock
  rw [dgCoherentBarStrictPrefixHom_eq_zero R D F s k hk h]
  simp only [moduleHomShiftBlock, zero_compose, compose_zero]

lemma dgCoherentBarStrictPrefixColumn_eq_zero {n : ℕ} (s : (nerve J) _⦋n⦌)
    (k : ℕ) (hk : 0 < k) (h : k + 1 ≤ n) :
    dgCoherentBarPrefixColumn R D (dgCoherentBarStrictDiagram R D F) s k h = 0 := by
  unfold dgCoherentBarPrefixColumn
  rw [dgCoherentBarStrictPrefixBlock_eq_zero R D F s k hk h, map_zero]

lemma dgCoherentBarStrictColumn {n : ℕ} (s : (nerve J) _⦋n + 1⦌) :
    dgCoherentBarColumn R D (dgCoherentBarStrictDiagram R D F) ⟨n + 1, s⟩ =
      (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
        dgCoherentBarFaceColumn R D (dgCoherentBarStrictDiagram R D F) s i) +
      ((n : ℤ) + 1).negOnePow •
        dgCoherentBarPrefixColumn R D (dgCoherentBarStrictDiagram R D F) s 0 (by omega) := by
  have hs : (∑ k : Fin (n + 1),
      dgCoherentBarPrefixColumn R D (dgCoherentBarStrictDiagram R D F) s k.val (by omega)) =
        dgCoherentBarPrefixColumn R D (dgCoherentBarStrictDiagram R D F) s 0 (by omega) := by
    apply Fintype.sum_eq_single (0 : Fin (n + 1))
    intro i hi
    exact dgCoherentBarStrictPrefixColumn_eq_zero R D F s i.val (by
      have h0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega) _
  change (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
    dgCoherentBarFaceColumn R D (dgCoherentBarStrictDiagram R D F) s i) +
      ((n : ℤ) + 1).negOnePow • (∑ k : Fin (n + 1),
        dgCoherentBarPrefixColumn R D (dgCoherentBarStrictDiagram R D F) s k.val (by omega)) = _
  rw [hs]

end SerrePositivity.InfinityCategories
