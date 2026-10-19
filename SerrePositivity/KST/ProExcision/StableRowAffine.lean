module
public import SerrePositivity.KST.ProExcision.StableColumnAffine
public import SerrePositivity.KST.ProExcision.RowLeftBlockCoherence

/-!
# 通常の有限 rank の行側半直積の実安定模型

概要：通常の右行列作用の実半直積を単体的モノイドの実 rank 余極限にする。
方針：実ブロック写像と実標準包含・左乗法を実自然変換に束ねる。
規約：KST Proposition 4.14、SW92 §1.2。係数の可換性を仮定しない。
使われ方：実安定行側相対ホモロジーの左乗法の零化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Opposite
open scoped Simplicial

/-- 概要：通常の実行側半直積のブロック安定化の rank 順序列。
方針：実一座標遷移を関手にする。
規約：SW92 §1.2。使われ方：実安定行側半直積の定義。 -/
def NonUnitalSimplicialRing.rowAffineRankSequence (I : NonUnitalSimplicialRing.{u}) :
    ℕ ⥤ SimplicialObject MonCat.{u} := Functor.ofSequence (fun n ↦ I.rowAffineBlockMap n 1)

/-- 概要：通常の実 ĜL rank 順序列の実行側半直積への標準包含。
方針：実ブロック写像の標準包含との可換性を一座標遷移で使う。
規約：KST Proposition 4.14。使われ方：実安定行側相対項の基準。 -/
def NonUnitalSimplicialRing.rowAffineSectionNatTrans (I : NonUnitalSimplicialRing.{u}) :
    I.hatGLRankSequence ⟶ I.rowAffineRankSequence :=
  NatTrans.ofSequence (fun n ↦ I.rowAffineSection n) (by
    intro n
    rw [show I.hatGLRankSequence.map (homOfLE (Nat.le_add_right n 1)) = I.hatGLBlockMap n 1 from
      Functor.ofSequence_map_homOfLE_succ _ _,
      show I.rowAffineRankSequence.map (homOfLE (Nat.le_add_right n 1)) = I.rowAffineBlockMap n 1 from
        Functor.ofSequence_map_homOfLE_succ _ _]
    exact (I.rowAffineBlockMap_section n 1).symm)

/-- 概要：通常の実行側半直積の実 rank 余極限。
方針：単体的モノイドの実余極限を取る。
規約：SW92 §1.2。使われ方：実安定行側の模型。 -/
def NonUnitalSimplicialRing.stableRowAffine (I : NonUnitalSimplicialRing.{u}) :
    SimplicialObject MonCat.{u} := colimit I.rowAffineRankSequence

/-- 概要：実安定 ĜL の実安定行側半直積への標準包含。
方針：有限 rank の実自然変換を余極限関手に写す。
規約：KST Proposition 4.14。使われ方：実安定行側相対 H_* の基準。 -/
def NonUnitalSimplicialRing.stableRowAffineSection (I : NonUnitalSimplicialRing.{u}) :
    I.stableHatGL ⟶ I.stableRowAffine := colimMap I.rowAffineSectionNatTrans

/-- 概要：通常の実行側半直積の rank 順序列への左乗法の実自然変換。
方針：通常の実ブロック安定化と実左乗法の可換性を使う。
規約：SW92 §1.2。使われ方：実安定行側の左乗法。 -/
def NonUnitalSimplicialRing.rowAffineLeftNatTrans (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) : I.rowAffineRankSequence ⟶ I.rowAffineRankSequence :=
  NatTrans.ofSequence (fun n ↦ I.rowAffineLeftMap a n) (by
    intro n
    rw [show I.rowAffineRankSequence.map (homOfLE (Nat.le_add_right n 1)) = I.rowAffineBlockMap n 1 from
      Functor.ofSequence_map_homOfLE_succ _ _]
    exact (I.rowAffineLeft_block_commute a n 1).symm)

/-- 概要：実安定行側半直積に行の左乗法を施す実自己射。
方針：実 rank 自然変換を余極限関手に写す。
規約：KST Proposition 4.14。零性を定義に含めない。
使われ方：実安定行側相対 H_* の実誘導写像。 -/
def NonUnitalSimplicialRing.stableRowAffineLeftMap (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) : I.stableRowAffine ⟶ I.stableRowAffine :=
  colimMap (I.rowAffineLeftNatTrans a)

end SerrePositivity.KST.ProExcision
