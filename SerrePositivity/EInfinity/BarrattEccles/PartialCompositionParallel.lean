module

public import SerrePositivity.EInfinity.BarrattEccles.ParallelTensor
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionInsertion
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionNested
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleParallelChains

/-!
# 部分合成の複体の射の並列結合則

概要：Berger–Fresse §1.1.3 の異なる入力への代入の交換を複体の射として証明する。
方針：三重純粋テンソルで交換の Koszul 符号と正規化鎖の並列結合則を比較する。
規約：出力 arity と中間 arity の移送を明示する。
使われ方：Barratt–Eccles オペラッドの parallel_assoc の公理となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：並列の部分合成は出力 arity の順方向の移送後に一致する（Berger–Fresse §1.1.3）。
方針：負の斉次テンソル上で正規化鎖の並列結合則を適用する。
規約：二つの代入位置は異なり、順序関係は要求しない。
使われ方：オペラッドの並列結合則の arity の移送を整理する。 -/
lemma partialComposition_parallel_assoc_forward (m n k : ℕ)
    (i j : Fin (m + 2)) (hji : j ≠ i) :
    (partialCompositionAfterInsertion A m n i ▷ complex A k) ≫
        partialComposition A (m + n) k (parallelSlot m n i j hji) ≫
        eqToHom (congrArg (complex A) (by omega : m + n + k = m + k + n)) =
      exchangeLastFactors (complex A (m + 2)) (complex A n) (complex A k) ≫
        (partialCompositionAfterInsertion A m k j ▷ complex A n) ≫
        partialComposition A (m + k) n (parallelSlot m k j i hji.symm) := by
  rw [← normalizedFunctor_arityMap A (by omega : m + n + k = m + k + n)]
  apply triple_complex_hom_ext A (m + 2) n k
  intro p q r x y z
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply
    (partialCompositionAfterInsertion A m n i) (complex A k)
    (-((p + q : ℕ) : ℤ)) (-(r : ℤ)) (-((p + q + r : ℕ) : ℤ)) (by omega)]
  rw [partialCompositionAfterInsertion_neg_tmul A m n i p q,
    partialComposition_neg_tmul A (m + n) k (parallelSlot m n i j hji) (p + q) r]
  erw [complexXIso_inv_naturality_apply A (m := m + n + k) (n := m + k + n)
    (simplicialArityMap (by omega : m + n + k = m + k + n)) (p + q + r)]
  rw [exchangeLastFactors_apply (complex A (m + 2)) (complex A n) (complex A k)
    (-(p : ℤ)) (-(q : ℤ)) (-(r : ℤ)) (-((p + q : ℕ) : ℤ))
    (-((q + r : ℕ) : ℤ)) (-((p + r : ℕ) : ℤ)) (-((p + q + r : ℕ) : ℤ))
    (by omega) (by omega) (by omega) (by omega)]
  simp only [Units.smul_def, map_zsmul]
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply
    (partialCompositionAfterInsertion A m k j) (complex A n)
    (-((p + r : ℕ) : ℤ)) (-(q : ℤ)) (-((p + q + r : ℕ) : ℤ)) (by omega)]
  rw [partialCompositionAfterInsertion_neg_tmul A m k j p r,
    partialComposition_neg_tmul_output A (m + k) n (parallelSlot m k j i hji.symm)
      (p + r) q (p + q + r) (by omega)]
  simp only [Iso.inv_hom_id_apply]
  have hs : ((-(q : ℤ) * -(r : ℤ)).negOnePow : ℤ) = (-1 : ℤ) ^ (q * r) := by
    rw [neg_mul_neg, ← Nat.cast_mul, Int.coe_negOnePow_natCast]
  rw [hs, ← map_zsmul]
  congr 1
  have h := shuffleBilinear_parallel_assoc A m n k i j hji p q r
    ((complexXIso A (m + 2) p).hom x) ((complexXIso A n q).hom y) ((complexXIso A k r).hom z)
  have ht := congrArg (degreeTransport A (m + k + n)
    (by omega : p + r + q = p + q + r)) h
  rw [degreeTransport_symm_cancel] at ht
  simpa only [map_zsmul] using ht

/-- 概要：部分合成の複体の射は Koszul braiding を介した並列結合則を満たす（Berger–Fresse §1.1.3）。
方針：順方向の arity の移送を逆移送で打ち消し、二つの位置を順序付きの式に直す。
規約：i<j の二入力に対する代入を比較する。
使われ方：対称オペラッドの parallel_assoc の公理を満たす。 -/
lemma partialComposition_parallel_assoc (m n k : ℕ)
    (i j : Fin (m + 2)) (hij : i.val < j.val) :
    (partialComposition A (m + 1) n i ▷ complex A k) ≫
        eqToHom (congrArg (fun q => complex A q ⊗ complex A k)
          (by omega : m + 1 + n = m + n + 1)) ≫
        partialComposition A (m + n) k ⟨j.val + n - 1, by omega⟩ =
      (α_ (complex A (m + 2)) (complex A n) (complex A k)).hom ≫
        (complex A (m + 2) ◁ (β_ (complex A n) (complex A k)).hom) ≫
        (α_ (complex A (m + 2)) (complex A k) (complex A n)).inv ≫
        (partialComposition A (m + 1) k j ▷ complex A n) ≫
        eqToHom (congrArg (fun q => complex A q ⊗ complex A n)
          (by omega : m + 1 + k = m + k + 1)) ≫
        partialComposition A (m + k) n ⟨i.val, by omega⟩ ≫
        eqToHom (congrArg (complex A) (by omega : m + k + n = m + n + k)) := by
  have hji : j ≠ i := fun h => by have hv := congrArg Fin.val h; omega
  have hL : parallelSlot m n i j hji = ⟨j.val + n - 1, by omega⟩ := by
    apply Fin.ext
    rw [parallelSlot_val]
    exact ite_eq_right (by omega)
  have hR : parallelSlot m k j i hji.symm = ⟨i.val, by omega⟩ := by
    apply Fin.ext
    rw [parallelSlot_val]
    exact ite_eq_left hij
  have h := congrArg
    (fun f => f ≫ eqToHom (congrArg (complex A) (by omega : m + k + n = m + n + k)))
    (partialComposition_parallel_assoc_forward A m n k i j hji)
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, hL, hR,
    partialCompositionAfterInsertion, exchangeLastFactors, comp_whiskerRight] at h
  rw [← arity_tensor_eqToHom A (by omega : m + 1 + n = m + n + 1) (complex A k),
    ← arity_tensor_eqToHom A (by omega : m + 1 + k = m + k + 1) (complex A n)] at h
  simpa only [Category.assoc] using h

end SerrePositivity.EInfinity.BarrattEccles
