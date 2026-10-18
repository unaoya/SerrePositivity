module
public import SerrePositivity.KST.ProExcision.SimplicialColumnRightMultiplication
public import SerrePositivity.KST.ProExcision.ColumnBlockPairCoherence
public import SerrePositivity.KST.ProExcision.Claim415

/-!
# 列の右乗法とブロック安定化の可換性

概要：右乗法と通常の rank 安定化を組み合わせた実対射を比較する。
方針：基底と列の成分を別々に計算する。
規約：KST Claim 4.15・Proposition 4.14 の (id,a)、非可換な右乗法。
使われ方：有限 rank の零化から実余極限の右乗法の零化へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：列の右乗法は零埋めと可換。
方針：元の行では同じ右積、追加した行では零の右積を計算する。
規約：KST Proposition 4.14、非可換な周囲環。
使われ方：同じ rank の右乗法の自然変換の安定化。 -/
lemma idealVectorRightHom_columnBlock {R : Type u} [Ring R] (J : TwoSidedIdeal R)
    (n m : ℕ) (a : R) (v : Multiplicative (Fin n → J)) :
    idealVectorRightHom J (Fin (n + m)) a ((columnBlockInclusion J n m).toMultiplicative v) =
      (columnBlockInclusion J n m).toMultiplicative (idealVectorRightHom J (Fin n) a v) := by
  change (fun i ↦ idealRightMultiplication J a (columnBlockInclusion J n m v.toAdd i)) =
    columnBlockInclusion J n m (fun i ↦ idealRightMultiplication J a (v.toAdd i))
  funext i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  cases i with
  | inl i => simp only [finSumFinEquiv_apply_left, columnBlockInclusion_left]
  | inr i => simp only [finSumFinEquiv_apply_right, columnBlockInclusion_right, map_zero]

/-- 概要：同じ rank の右乗法の後のブロック安定化は Claim 4.15 の実対射に等しい。
方針：Claim 4.15 の通常の基底・列の両成分の式で比較する。
規約：KST Claim 4.15。使われ方：相対写像の零化を安定右乗法へ接続する。 -/
lemma NonUnitalSimplicialRing.columnRight_then_block (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n m : ℕ) :
    (I.columnRightActionHom a n).toPairMap.comp (I.columnBlockOverHom n m).toPairMap =
      claim415ColumnPairMap I a n m := by
  apply SimplicialActionPairMap.ext_of_maps
  · rfl
  · apply NatTrans.ext
    funext k
    rcases k with ⟨⟨q⟩⟩
    letI := (I.hatGLColumnAction n).actionStructure (op ⦋q⦌)
    letI := (I.hatGLColumnAction (n + m)).actionStructure (op ⦋q⦌)
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    change ActionProduct (I.hatGLSubmonoid n q)
      (Multiplicative (Fin n → integerUnitizationIdeal (I.obj (op ⦋q⦌)))) at x
    apply ActionProduct.ext
    · exact (claim415ColumnPairMap_base I a n m q x).symm
    · exact (claim415ColumnPairMap_fiber I a n m q x).symm

/-- 概要：ブロック安定化と同じ rank の右乗法は実対射として可換。
方針：基底は恒等射の消去、列は右乗法と零埋めの可換性を使う。
規約：KST Proposition 4.14、(id,a) の rank 自然性。
使われ方：相対アフィン加群の実順序列の自己自然変換。 -/
lemma NonUnitalSimplicialRing.columnRight_block_commute (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n m : ℕ) :
    (I.columnRightActionHom a n).toPairMap.comp (I.columnBlockOverHom n m).toPairMap =
      (I.columnBlockOverHom n m).toPairMap.comp (I.columnRightActionHom a (n + m)).toPairMap := by
  apply SimplicialActionPairMap.ext_of_maps
  · simp only [SimplicialActionPairMap.comp, SimplicialActionHom.toPairMap,
      SimplicialActionOverHom.toPairMap, Category.id_comp, Category.comp_id]
  · apply NatTrans.ext
    funext k
    rcases k with ⟨⟨q⟩⟩
    letI := (I.hatGLColumnAction n).actionStructure (op ⦋q⦌)
    letI := (I.hatGLColumnAction (n + m)).actionStructure (op ⦋q⦌)
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply ActionProduct.ext
    · rfl
    · exact (idealVectorRightHom_columnBlock _ n m _ x.fiber).symm

end SerrePositivity.KST.ProExcision
