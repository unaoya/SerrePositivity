module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VectorTensorAppendTransport

/-!
模型。文献の定義との比較は後で
# 元のappendIsoによる同じ斉次テンソルの連結

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §293。
区間の面に限らず同じ複体の斉次因子で、左単位子・結合子をそのまま評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- 概要：appendIso は二つの面テンソルを連結した面テンソルへ送る（BF §2.2.6）。
方針：先頭面を保ち、結合子と尾の連結の帰納法で計算する。
規約：同じ指定整数全次数で評価する。
使われ方：二段余演算の出力を共通の面テンソル族に戻す。 -/
lemma appendIso_vectorTensor (K : Complex A) (m n : ℕ)
    (f : Fin m → Σ d : ℕ, K.X (-(d : ℤ))) (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (t : ℤ) (ht : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ) = t) :
    (appendIso K m n).hom.f t
      (ιTensorObj (power K m) (power K n)
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ)) t ht
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K m f ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K n g)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (m + n) (Fin.append f g) t
        (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append]; omega) := by
  induction m generalizing t with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum, Nat.cast_zero, neg_zero, zero_add] at ht
    cases ht
    change (eqToHom (congrArg (power K) (Nat.zero_add n).symm)).f _
      ((λ_ (power K n)).hom.f _
        (ιTensorObj (𝟙_ (Complex A)) (power K n) 0 _ _ (zero_add _)
          ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) ⊗ₜ[A]
            _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K n g))) = _
    rw [leftUnitor_hom_generator]
    simpa only [Fin.append_left_nil f g rfl, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_refl] using
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_arity_transport K (Nat.zero_add n).symm g _ rfl
  | succ m ih =>
    obtain ⟨a, f, rfl⟩ := Fin.exists_cons f
    have hsum : -(a.1 : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ) =
        -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (m + 1) (Fin.cons a f) : ℤ) := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cons]
      omega
    change (eqToHom (congrArg (power K) (Nat.succ_add m n).symm)).f t
      ((K ◁ (appendIso K m n).hom).f t
        ((α_ K (power K m) (power K n)).hom.f t
          (ιTensorObj (K ⊗ power K m) (power K n)
            _ _ t ht (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K (m + 1) (Fin.cons a f) ⊗ₜ[A]
              _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K n g)))) = _
    have hvec := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_cons K m a f _ hsum
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_refl] at hvec
    rw [hvec, associator_apply_of_sum, SerrePositivity.DifferentialGraded.whiskerLeft_apply]
    rw [ih f (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ)) rfl]
    have hs : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (m + n) (Fin.append f g) : ℤ) =
        -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ) := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append]
      omega
    have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_succ K (m + n) (Fin.cons a (Fin.append f g))
      (-(a.1 : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ)) t
      rfl hs (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cons] at ht; omega)
    have H' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (m + n + 1) (Fin.cons a (Fin.append f g)) t (by
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append, Nat.cast_add] at ht ⊢; omega) =
        ιTensorObj K (power K (m + n)) (-(a.1 : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ)) t
          (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cons] at ht; omega)
          (a.2 ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (m + n) (Fin.append f g)
            (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ)) hs) := by
      simpa only [Fin.cons_zero, Fin.cons_succ, eqToHom_refl, ModuleCat.id_apply] using! H
    rw [← H']
    simpa only [Fin.append_cons] using! _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_arity_transport K
      (Nat.succ_add m n).symm (Fin.cons a (Fin.append f g)) t (by
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append, Nat.cast_add] at ht ⊢; omega)

/-- 概要：指定整数次数の面テンソルも appendIso で連結される（BF §2.2.6）。
方針：二つの入力次数の等式を消去して自然な面テンソルの連結公式へ戻す。
規約：前後の次数と全次数を個別に指定する。
使われ方：余演算の係数次数と出力次数に合わせた連結評価。 -/
lemma appendIso_vectorTensorAt (K : Complex A) (m n : ℕ)
    (f : Fin m → Σ d : ℕ, K.X (-(d : ℤ))) (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (r s t : ℤ) (hr : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ) = r) (hs : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ) = s)
    (ht : r + s = t) :
    (appendIso K m n).hom.f t
      (ιTensorObj (power K m) (power K n) r s t ht
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K m f r hr ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K n g s hs)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (m + n) (Fin.append f g) t
        (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append]; omega) := by
  cases hr
  cases hs
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_refl]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.appendIso_vectorTensor K m n f g t ht

/-- 概要：appendIso の逆は連結した面テンソルを元の前後のテンソルへ分ける（BF §2.2.6）。
方針：順方向の連結等式に逆射を適用して同型の往復を消す。
規約：指定整数全次数を保持し、空の前後列も含む。
使われ方：指定出力への代入で出力列を前後へ分割する。 -/
lemma appendIso_inv_vectorTensorAt (K : Complex A) (m n : ℕ)
    (f : Fin m → Σ d : ℕ, K.X (-(d : ℤ))) (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (r s t : ℤ) (hr : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K m f : ℤ) = r) (hs : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ) = s)
    (ht : r + s = t) :
    (appendIso K m n).inv.f t
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (m + n) (Fin.append f g) t
        (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append]; omega)) =
      ιTensorObj (power K m) (power K n) r s t ht
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K m f r hr ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K n g s hs) := by
  have H := congrArg (fun x => (appendIso K m n).inv.f t x)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.appendIso_vectorTensorAt K m n f g r s t hr hs ht)
  have he : (appendIso K m n).inv.f t
      ((appendIso K m n).hom.f t
        (ιTensorObj (power K m) (power K n) r s t ht
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K m f r hr ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K n g s hs))) =
      ιTensorObj (power K m) (power K n) r s t ht
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K m f r hr ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K n g s hs) := by
    change ((appendIso K m n).hom ≫ (appendIso K m n).inv).f t _ = _
    rw [Iso.hom_inv_id]
    rfl
  rw [he] at H
  exact H.symm


end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
