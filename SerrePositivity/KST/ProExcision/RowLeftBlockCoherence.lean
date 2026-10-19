module
public import SerrePositivity.KST.ProExcision.SimplicialRowLeftMultiplication
public import SerrePositivity.KST.ProExcision.SimplicialRowBlockInclusion

/-!
# 行側の実左乗法と通常の rank 安定化の実可換性

概要：行の実左乗法と実零埋めが可換であることを示す。
方針：前半の座標と後半の零座標で指定元の実左乗法を評価する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実安定行側の左乗法自然変換。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：イデアル内の実左乗法は通常のベクトルの零埋めと可換。
方針：前半は同じ積、後半は零の左積を使う。
規約：SW92 §1.2、中心性不要。使われ方：行側の実 rank 自然性。 -/
lemma idealVectorLeftHom_block {R : Type u} [Ring R] (J : TwoSidedIdeal R)
    (n m : ℕ) (a : R) (v : Multiplicative (Fin n → J)) :
    idealVectorLeftHom J (Fin (n + m)) a ((columnBlockInclusion J n m).toMultiplicative v) =
      (columnBlockInclusion J n m).toMultiplicative (idealVectorLeftHom J (Fin n) a v) := by
  change (fun i ↦ idealLeftMultiplication J a (columnBlockInclusion J n m v.toAdd i)) =
    columnBlockInclusion J n m (fun i ↦ idealLeftMultiplication J a (v.toAdd i))
  funext i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  cases i with
  | inl i => simp only [finSumFinEquiv_apply_left, columnBlockInclusion_left]
  | inr i => simp only [finSumFinEquiv_apply_right, columnBlockInclusion_right, map_zero]

/-- 概要：実行側半直積の左乗法は通常のブロック安定化と可換。
方針：基底は恒等、行成分は実零埋めとの可換性を使う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実安定左乗法の構成。 -/
lemma NonUnitalSimplicialRing.rowAffineLeft_block_commute
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n m : ℕ) :
    I.rowAffineLeftMap a n ≫ I.rowAffineBlockMap n m =
      I.rowAffineBlockMap n m ≫ I.rowAffineLeftMap a (n + m) := by
  apply NatTrans.ext
  funext k
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro x
  apply MulOpposite.unop_injective
  apply ActionProduct.ext
  · rfl
  · exact (idealVectorLeftHom_block (I.standardIdeal.ideal k) n m
      (I.standardIdeal.vertexElement (I.standardElement a) k).val (MulOpposite.unop x).fiber).symm

end SerrePositivity.KST.ProExcision
