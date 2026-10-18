module

public import SerrePositivity.EInfinity.Operad.IteratedCompositionEquivariance

/-!
# 未代入入力の有限全単射と反復合成

概要：Berger–Moerdijk §1 の前方の入力への反復合成が、未代入の尾の有限全単射と両立することを示す。
方針：内側入力の置換を恒等にした等変性を使い、尾の長さの等式で異なる表記を同一視する。
規約：前方の各入力ブロックの順序と内部の順序は変えない。
使われ方：末尾二入力の外側交換を、残りの反復合成における尾の全単射として移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open scoped BigOperators

/-- 概要：各ブロックの恒等置換を連結した置換は恒等である（Berger–Moerdijk §1）。
方針：ブロック数で帰納し、ブロック和と共役が恒等を保つことを使う。
規約：零長の入力ブロックも許す。
使われ方：反復合成の内側の置換を恒等にして尾だけの等変性を取り出す。 -/
lemma tensorFamilyPermutation_refl (n : ℕ) (s : Fin n → ℕ) :
    tensorFamilyPermutation n s (fun i => Equiv.refl (Fin (s i))) =
      Equiv.refl (Fin (∑ i, s i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tensorFamilyPermutation, ih, FiniteBijection.blockEquiv_refl,
      Equiv.permCongr_refl]

namespace Operad

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 概要：前方への反復合成は未代入の尾の置換と両立する（Berger–Moerdijk §1）。
方針：内側の全ての置換を恒等にした反復合成の等変性を適用する。
規約：前方 n 個へ代入し、尾 k 個を残す。
使われ方：隣接二入力の交換後の出力の置換を残りの反復合成の後へ移す。 -/
lemma composeFirstInputs_tail_equivariance (P : Operad A) (n k : ℕ) (s : Fin n → ℕ)
    (ρ : Equiv.Perm (Fin k)) :
    (P.sequence.map (FiniteBijection.permutation (n + k)
        (FiniteBijection.blockEquiv (Equiv.refl (Fin n)) ρ)) ▷
      tensorFamily n (fun i => P.arity (s i))) ≫ P.composeFirstInputs n k s =
      P.composeFirstInputs n k s ≫ P.sequence.map
        (FiniteBijection.permutation ((∑ i, s i) + k)
          (FiniteBijection.blockEquiv (Equiv.refl (Fin (∑ i, s i))) ρ)) := by
  have hid (m : ℕ) : P.sequence.map
      (FiniteBijection.permutation m (Equiv.refl (Fin m))) = 𝟙 (P.arity m) := by
    change P.sequence.map (FiniteBijection.permutation m (1 : Equiv.Perm (Fin m))) = _
    rw [FiniteBijection.permutation_one, P.sequence.map_id]
    rfl
  have h := P.composeFirstInputs_equivariance n k s
    (fun i => Equiv.refl (Fin (s i))) ρ
  simp only [hid, tensorFamilyPermutation_refl] at h
  rw [tensorFamilyMap_id n (fun i => P.arity (s i))] at h
  rw [tensorHom_id (P.sequence.map (FiniteBijection.permutation (n + k)
    (FiniteBijection.blockEquiv (Equiv.refl (Fin n)) ρ)))
    (tensorFamily n (fun i => P.arity (s i)))] at h
  exact h

/-- 概要：前方への反復合成は尾の任意の有限全単射と両立する（Berger–Moerdijk §1）。
方針：全単射で尾の長さが等しいことを使い、同じ長さの置換の等変性へ帰着する。
規約：尾の始域と終域の長さの式は異なってよい。
使われ方：ブロック交換で長さの表記が変わる尾を残りの反復合成へ移す。 -/
lemma composeFirstInputs_tail_bijection (P : Operad A) (n k l : ℕ) (s : Fin n → ℕ)
    (e : Fin k ≃ Fin l) :
    (P.sequence.map (FiniteBijection.homOfEquiv (X := FiniteBijection.of (n + k))
        (Y := FiniteBijection.of (n + l)) (FiniteBijection.blockEquiv (Equiv.refl (Fin n)) e)) ▷
      tensorFamily n (fun i => P.arity (s i))) ≫ P.composeFirstInputs n l s =
      P.composeFirstInputs n k s ≫ P.sequence.map
        (FiniteBijection.homOfEquiv (X := FiniteBijection.of ((∑ i, s i) + k))
          (Y := FiniteBijection.of ((∑ i, s i) + l))
          (FiniteBijection.blockEquiv (Equiv.refl (Fin (∑ i, s i))) e)) := by
  have hkl : k = l := Fin.equiv_iff_eq.mp ⟨e⟩
  subst l
  exact P.composeFirstInputs_tail_equivariance n k s e

end Operad

end SerrePositivity.EInfinity
