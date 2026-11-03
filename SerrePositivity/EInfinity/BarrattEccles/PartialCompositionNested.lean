module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleNestedChains
public import SerrePositivity.EInfinity.BarrattEccles.TripleComplexExt
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionLeftUnit
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# 部分合成の複体の射の入れ子結合則

概要：Berger–Fresse §1.1.3 の shuffle 部分合成の入れ子結合則を複体の射として証明する。
方針：負の斉次三重テンソルで評価し、正規化鎖上の結合則を適用する。
規約：出力 arity の加法の結合則は等式の射で移送する。
使われ方：Barratt–Eccles オペラッドの入れ子結合則となる。
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

/-- 概要：次数の移送は逆の移送と打ち消し合う（Berger–Fresse §1.1.2）。
方針：次数の等式を消去する。
規約：正規化鎖の同じ arity 内で移送する。
使われ方：入れ子結合則の出力次数を左括弧へ合わせる。 -/
lemma degreeTransport_symm_cancel (n : ℕ) {p q : ℕ} (h : p = q)
    (x : (normalizedChains A n).X p) :
    degreeTransport A n h.symm (degreeTransport A n h x) = x := by
  cases h
  rfl

/-- 概要：部分合成の入れ子結合則は出力 arity の順方向の移送後に成立する（Berger–Fresse §1.1.3）。
方針：三重純粋テンソルで評価し、正規化鎖の入れ子結合則へ帰着する。
規約：両辺の出力 arity は m+(n+k) とする。
使われ方：オペラッドの入れ子結合則の等式の射を整理する。 -/
lemma partialComposition_nested_assoc_forward (m n k : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (partialComposition A m (n + 1) i ▷ complex A k) ≫
        partialComposition A (m + n) k (nestedSlot m n i j) ≫
        eqToHom (congrArg (complex A) (Nat.add_assoc m n k)) =
      (α_ (complex A (m + 1)) (complex A (n + 1)) (complex A k)).hom ≫
        (complex A (m + 1) ◁ partialComposition A n k j) ≫
        partialComposition A m (n + k) i := by
  rw [← normalizedFunctor_arityMap A (Nat.add_assoc m n k)]
  apply triple_complex_hom_ext A (m + 1) (n + 1) k
  intro p q r x y z
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply
    (partialComposition A m (n + 1) i) (complex A k)
    (-((p + q : ℕ) : ℤ)) (-(r : ℤ)) (-((p + q + r : ℕ) : ℤ)) (by omega)]
  erw [partialComposition_neg_tmul A m (n + 1) i p q]
  erw [partialComposition_neg_tmul A (m + n) k (nestedSlot m n i j) (p + q) r]
  erw [complexXIso_inv_naturality_apply A (m := m + n + k) (n := m + (n + k))
    (simplicialArityMap (Nat.add_assoc m n k)) (p + q + r)]
  rw [SerrePositivity.DifferentialGraded.associator_apply_of_sums
    (complex A (m + 1)) (complex A (n + 1)) (complex A k)
    (-(p : ℤ)) (-(q : ℤ)) (-(r : ℤ)) (-((p + q : ℕ) : ℤ))
    (-((q + r : ℕ) : ℤ)) (-((p + q + r : ℕ) : ℤ)) (by omega) (by omega) (by omega)]
  rw [SerrePositivity.DifferentialGraded.whiskerLeft_apply
    (complex A (m + 1)) (partialComposition A n k j)
    (-(p : ℤ)) (-((q + r : ℕ) : ℤ)) (-((p + q + r : ℕ) : ℤ)) (by omega)]
  rw [partialComposition_neg_tmul A n k j q r]
  rw [partialComposition_neg_tmul_output A m (n + k) i p (q + r) (p + q + r)
    (Nat.add_assoc p q r).symm]
  simp only [Iso.inv_hom_id_apply]
  congr 1
  have hc (w : (normalizedChains A (m + (n + 1))).X (p + q)) :
      (complexXIso A (m + n + 1) (p + q)).hom
        ((complexXIso A (m + (n + 1)) (p + q)).inv w) = w :=
    congrArg (fun f => f w) (complexXIso A (m + (n + 1)) (p + q)).inv_hom_id
  rw [hc]
  have h := shuffleBilinear_nested_assoc A m n k i j p q r
    ((complexXIso A (m + 1) p).hom x) ((complexXIso A (n + 1) q).hom y)
    ((complexXIso A k r).hom z)
  have ht := congrArg (degreeTransport A (m + (n + k)) (Nat.add_assoc p q r).symm) h
  rw [degreeTransport_symm_cancel] at ht
  exact ht

/-- 概要：shuffle 部分合成の複体の射は入れ子の結合則を満たす（Berger–Fresse §1.1.3）。
方針：順方向の arity の移送を逆向きの等式の射で打ち消す。
規約：二回目の代入位置は i+j、右辺の最後に出力 arity を移送する。
使われ方：対称オペラッドの nested_assoc の公理を満たす。 -/
lemma partialComposition_nested_assoc (m n k : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (partialComposition A m (n + 1) i ▷ complex A k) ≫
        partialComposition A (m + n) k ⟨i.val + j.val, by omega⟩ =
      (α_ (complex A (m + 1)) (complex A (n + 1)) (complex A k)).hom ≫
        (complex A (m + 1) ◁ partialComposition A n k j) ≫
        partialComposition A m (n + k) i ≫
        eqToHom (congrArg (complex A) (Nat.add_assoc m n k).symm) := by
  have hslot : nestedSlot m n i j = ⟨i.val + j.val, by omega⟩ :=
    Fin.ext (insertedPosition_val m (n + 1) i j)
  rw [← hslot]
  have h := congrArg
    (fun f => f ≫ eqToHom (congrArg (complex A) (Nat.add_assoc m n k).symm))
    (partialComposition_nested_assoc_forward A m n k i j)
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h

end SerrePositivity.EInfinity.BarrattEccles
