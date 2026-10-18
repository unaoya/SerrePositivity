module
public import SerrePositivity.KST.ProExcision.IdealVectorMap

/-!
# 実列の群準同型の係数変更に関する自然性

概要：イデアルを保つ環準同型は ψ と最後の列の右乗法 φ と可換。
方針：実列の有限和と準同型の単位・加法・乗法保存を使う。
規約：KST Lemma 4.16 の (I,a) に関する関手性、非可換な係数。
使われ方：A.5 の因子データを異なる係数環の間で接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} {R' : Type v} [Ring R] [Ring R']

/-- 概要：補助列の実行列は係数準同型に自然。
方針：各単一成分行列の有限和に準同型を適用する。
規約：KST 4.16。使われ方：ψ の群準同型の係数自然性。 -/
lemma blockColumn_coefficient_map {ι : Type w} {κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : R →+* R') (r : ι → κ) (p : κ) (v : ι → R) :
    (blockColumn r p v).map f = blockColumn r p (fun i ↦ f (v i)) := by
  ext i j
  simp only [Matrix.map_apply, blockColumn, Matrix.sum_apply, Matrix.single_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp only [map_zero]

/-- 概要：イデアル内の実補助列の群準同型は係数変更に自然。
方針：実群の係数写像の値を展開し、1 と補助列の像を同定する。
規約：KST 4.16。使われ方：最後の列と補助列の自然性。 -/
lemma idealBlockColumnHom_functorial {ι : Type w} [Fintype ι]
    (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J')
    (r : ι → Fin (n + m)) (p : Fin (n + m)) (hr : ∀ i, r i < p) (hp : n ≤ p.val)
    (v : Multiplicative (ι → J)) :
    triangularBlockGroupMap n m J J' f hf (idealBlockColumnHom n m J r p hr hp v) =
      idealBlockColumnHom n m J' r p hr hp (idealVectorMap J J' ι f hf v) := by
  apply Subtype.ext
  apply Units.ext
  rw [triangularBlockGroupMap_val]
  change (f.mapMatrix : Matrix (Fin (n + m)) (Fin (n + m)) R →+*
    Matrix (Fin (n + m)) (Fin (n + m)) R')
    (1 + blockColumn r p (fun i ↦ (v.toAdd i : R))) =
      1 + blockColumn r p (fun i ↦ f (v.toAdd i : R))
  rw [map_add, map_one]
  change 1 + (blockColumn r p (fun i ↦ (v.toAdd i : R))).map f = _
  rw [blockColumn_coefficient_map]

/-- 概要：最後の列に入れた右乗法は指定元を保つ係数変更に自然。
方針：列の準同型の自然性とイデアル内の右乗法の自然性を合成する。
規約：KST Lemma 4.16 の非可換な φ と (I,a) の射。
使われ方：帰納ホモトピーの第一入力 α の関手性。 -/
lemma lastRightColumnHom_functorial (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (a : R) (a' : R') (ha : f a = a')
    (v : Multiplicative (Fin n → J)) :
    lastRightColumnHom n m J' a' (idealVectorMap J J' (Fin n) f hf v) =
      triangularBlockGroupMap n (m + 1) J J' f hf (lastRightColumnHom n m J a v) := by
  change lastBlockColumnHom n m J' (idealVectorRightHom J' (Fin n) a'
    (idealVectorMap J J' (Fin n) f hf v)) = _
  rw [idealVectorRightHom_functorial J J' (Fin n) f hf a a' ha]
  exact (idealBlockColumnHom_functorial n (m + 1) J J' f hf _ _ _ _ _).symm

/-- 概要：直前の補助列 ψ の実群準同型は係数変更に自然。
方針：一般の実補助列の自然性を補助座標へ適用する。
規約：KST 4.16。使われ方：共役比較と μ の第二因子の関手性。 -/
lemma auxiliaryBlockColumnHom_functorial (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (v : Multiplicative (Fin n → J)) :
    auxiliaryBlockColumnHom n m J' (idealVectorMap J J' (Fin n) f hf v) =
      triangularBlockGroupMap n (m + 2) J J' f hf (auxiliaryBlockColumnHom n m J v) :=
  (idealBlockColumnHom_functorial n (m + 2) J J' f hf _ _ _ _ v).symm

end SerrePositivity.KST.ProExcision
