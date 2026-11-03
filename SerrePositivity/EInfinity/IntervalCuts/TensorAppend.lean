module

public import SerrePositivity.EInfinity.IntervalCuts.TupleAppend
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin

/-!
# 実際の区間面テンソルの連結

概要：Berger–Fresse §2.2.6 の面テンソルの連結を既存の appendIso で評価する。
方針：前方因子数で帰納し、左単位子・結合子・尾の連結を斉次元で計算する。
規約：空の前方・後方因子列を含む。
使われ方：指定出力への余演算の代入の実際のテンソル評価。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：appendIso は二つの面テンソルを連結した面テンソルへ送る（BF §2.2.6）。
方針：先頭面を保ち、結合子と尾の連結の帰納法で計算する。
規約：同じ指定整数全次数で評価する。
使われ方：二段余演算の出力を共通の面テンソル族に戻す。 -/
lemma appendIso_tensorVector (m n : ℕ) (f : Fin m → Simplex) (g : Fin n → Simplex)
    (t : ℤ) (ht : -(tupleDegree m f : ℤ) + -(tupleDegree n g : ℤ) = t) :
    (appendIso (interval A) m n).hom.f t
      (ιTensorObj (power (interval A) m) (power (interval A) n)
        (-(tupleDegree m f : ℤ)) (-(tupleDegree n g : ℤ)) t ht
        (tensorVector A m f ⊗ₜ[A] tensorVector A n g)) =
      tensorVectorAt A (m + n) (Fin.append f g) t
        (by rw [tupleDegree_append]; omega) := by
  induction m generalizing t with
  | zero =>
    simp only [tupleDegree, Nat.cast_zero, neg_zero, zero_add] at ht
    cases ht
    change (eqToHom (congrArg (power (interval A)) (Nat.zero_add n).symm)).f _
      ((λ_ (power (interval A) n)).hom.f _
        (ιTensorObj (𝟙_ (Complex A)) (power (interval A) n) 0 _ _ (zero_add _)
          ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) ⊗ₜ[A]
            tensorVector A n g))) = _
    rw [leftUnitor_hom_generator]
    simpa only [Fin.append_left_nil f g rfl, tensorVectorAt_refl] using
      tensorVectorAt_arity_transport A (Nat.zero_add n).symm g _ rfl
  | succ m ih =>
    obtain ⟨a, f, rfl⟩ := Fin.exists_cons f
    have hsum : -(simplexDegree a : ℤ) + -(tupleDegree m f : ℤ) =
        -(tupleDegree (m + 1) (Fin.cons a f) : ℤ) := by
      rw [tupleDegree_cons]
      omega
    change (eqToHom (congrArg (power (interval A)) (Nat.succ_add m n).symm)).f t
      (((interval A) ◁ (appendIso (interval A) m n).hom).f t
        ((α_ (interval A) (power (interval A) m) (power (interval A) n)).hom.f t
          (ιTensorObj ((interval A) ⊗ power (interval A) m) (power (interval A) n)
            _ _ t ht (tensorVector A (m + 1) (Fin.cons a f) ⊗ₜ[A]
              tensorVector A n g)))) = _
    have hvec := tensorVectorAt_cons A m a f _ hsum
    rw [tensorVectorAt_refl] at hvec
    rw [hvec, associator_apply_of_sum, SerrePositivity.DifferentialGraded.whiskerLeft_apply]
    rw [ih f (-(tupleDegree m f : ℤ) + -(tupleDegree n g : ℤ)) rfl]
    have hs : -(tupleDegree (m + n) (Fin.append f g) : ℤ) =
        -(tupleDegree m f : ℤ) + -(tupleDegree n g : ℤ) := by
      rw [tupleDegree_append]
      omega
    have H := tensorVectorAt_succ A (m + n) (Fin.cons a (Fin.append f g))
      (-(simplexDegree a : ℤ)) (-(tupleDegree m f : ℤ) + -(tupleDegree n g : ℤ)) t
      rfl hs (by rw [tupleDegree_cons] at ht; omega)
    have H' : tensorVectorAt A (m + n + 1) (Fin.cons a (Fin.append f g)) t (by
        simp only [tupleDegree_cons, tupleDegree_append, Nat.cast_add] at ht ⊢; omega) =
        ιTensorObj (interval A) (power (interval A) (m + n)) (-(simplexDegree a : ℤ))
          (-(tupleDegree m f : ℤ) + -(tupleDegree n g : ℤ)) t
          (by rw [tupleDegree_cons] at ht; omega)
          (faceVector A a ⊗ₜ[A] tensorVectorAt A (m + n) (Fin.append f g)
            (-(tupleDegree m f : ℤ) + -(tupleDegree n g : ℤ)) hs) := by
      simpa only [Fin.cons_zero, Fin.cons_succ, eqToHom_refl, ModuleCat.id_apply] using! H
    rw [← H']
    simpa only [Fin.append_cons] using! tensorVectorAt_arity_transport A
      (Nat.succ_add m n).symm (Fin.cons a (Fin.append f g)) t (by
        simp only [tupleDegree_cons, tupleDegree_append, Nat.cast_add] at ht ⊢; omega)

/-- 概要：指定整数次数の面テンソルも appendIso で連結される（BF §2.2.6）。
方針：二つの入力次数の等式を消去して自然な面テンソルの連結公式へ戻す。
規約：前後の次数と全次数を個別に指定する。
使われ方：余演算の係数次数と出力次数に合わせた連結評価。 -/
lemma appendIso_tensorVectorAt (m n : ℕ) (f : Fin m → Simplex) (g : Fin n → Simplex)
    (r s t : ℤ) (hr : -(tupleDegree m f : ℤ) = r) (hs : -(tupleDegree n g : ℤ) = s)
    (ht : r + s = t) :
    (appendIso (interval A) m n).hom.f t
      (ιTensorObj (power (interval A) m) (power (interval A) n) r s t ht
        (tensorVectorAt A m f r hr ⊗ₜ[A] tensorVectorAt A n g s hs)) =
      tensorVectorAt A (m + n) (Fin.append f g) t
        (by rw [tupleDegree_append]; omega) := by
  cases hr
  cases hs
  simp only [tensorVectorAt_refl]
  exact appendIso_tensorVector A m n f g t ht

/-- 概要：appendIso の逆は連結した面テンソルを元の前後のテンソルへ分ける（BF §2.2.6）。
方針：順方向の連結等式に逆射を適用して同型の往復を消す。
規約：指定整数全次数を保持し、空の前後列も含む。
使われ方：指定出力への代入で出力列を前後へ分割する。 -/
lemma appendIso_inv_tensorVectorAt (m n : ℕ) (f : Fin m → Simplex) (g : Fin n → Simplex)
    (r s t : ℤ) (hr : -(tupleDegree m f : ℤ) = r) (hs : -(tupleDegree n g : ℤ) = s)
    (ht : r + s = t) :
    (appendIso (interval A) m n).inv.f t
      (tensorVectorAt A (m + n) (Fin.append f g) t
        (by rw [tupleDegree_append]; omega)) =
      ιTensorObj (power (interval A) m) (power (interval A) n) r s t ht
        (tensorVectorAt A m f r hr ⊗ₜ[A] tensorVectorAt A n g s hs) := by
  have H := congrArg (fun x => (appendIso (interval A) m n).inv.f t x)
    (appendIso_tensorVectorAt A m n f g r s t hr hs ht)
  have he : (appendIso (interval A) m n).inv.f t
      ((appendIso (interval A) m n).hom.f t
        (ιTensorObj (power (interval A) m) (power (interval A) n) r s t ht
          (tensorVectorAt A m f r hr ⊗ₜ[A] tensorVectorAt A n g s hs))) =
      ιTensorObj (power (interval A) m) (power (interval A) n) r s t ht
        (tensorVectorAt A m f r hr ⊗ₜ[A] tensorVectorAt A n g s hs) := by
    change ((appendIso (interval A) m n).hom ≫ (appendIso (interval A) m n).inv).f t _ = _
    rw [Iso.hom_inv_id]
    rfl
  rw [he] at H
  exact H.symm

end SerrePositivity.EInfinity.IntervalCuts
