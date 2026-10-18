module
public import SerrePositivity.KST.ProExcision.BlockCoefficientMap
public import SerrePositivity.KST.ProExcision.Lemma416EquivariantData

/-!
# Lemma 4.16 の μ 版実データの係数自然性

概要：指定元と係数イデアルを保つ環準同型は帰納法の μ と積の群準同型と可換。
方針：実ブロック挿入、実列、右乗法の自然性を積に適用する。
規約：KST Lemma 4.16 の非可換版の (I,a) に関する関手性。
使われ方：実帰納ホモトピーを異なる係数環間で比較する A.5 の入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} {R' : Type v} [Ring R] [Ring R']

/-- 概要：μ の実群準同型は係数変更に自然。
方針：実埋め込みと ψ の自然性、係数写像の乗法保存を使う。
規約：KST 4.16 と A.5 の非可換な μ。
使われ方：異なる係数環間の A.5 の入力。 -/
lemma lemma416GroupData_mu_functorial (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (a : R) (a' : R')
    (p : triangularBlockGroup n (m + 1) J) (q : Multiplicative (Fin n → J)) :
    (lemma416GroupData n m J' a').μ
      (triangularBlockGroupMap n (m + 1) J J' f hf p, idealVectorMap J J' (Fin n) f hf q) =
    triangularBlockGroupMap n (m + 2) J J' f hf ((lemma416GroupData n m J a).μ (p, q)) := by
  rw [lemma416GroupData_mu_apply, lemma416GroupData_mu_apply,
    triangularBlockInsertion_functorial, auxiliaryBlockColumnHom_functorial, map_mul]

/-- 概要：A.5 の実積の群準同型は指定元を保つ係数変更に自然。
方針：積を φ と ψ へ分け、それぞれの自然性を使う。
規約：KST 4.16、右乗法 v_i a の順序を固定する。
使われ方：連結時に引く中間射の定数区間の自然性。 -/
lemma lemma416GroupData_product_functorial (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (a : R) (a' : R') (ha : f a = a')
    (v : Multiplicative (Fin n → J)) :
    (lemma416GroupData n m J' a').product (idealVectorMap J J' (Fin n) f hf v) =
    triangularBlockGroupMap n (m + 2) J J' f hf ((lemma416GroupData n m J a).product v) := by
  rw [GroupProductData.product_apply, GroupProductData.product_apply,
    lemma416GroupData_left, lemma416GroupData_right, lemma416GroupData_left, lemma416GroupData_right,
    lastRightColumnHom_functorial n (m + 1) J J' f hf a a' ha,
    auxiliaryBlockColumnHom_functorial, map_mul]

end SerrePositivity.KST.ProExcision
