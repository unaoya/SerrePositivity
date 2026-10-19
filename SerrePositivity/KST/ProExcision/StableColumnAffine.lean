module
public import SerrePositivity.KST.ProExcision.NonUnitalStableHatGL
public import SerrePositivity.KST.ProExcision.RelativeAffineRightMultiplication
public import SerrePositivity.KST.ProExcision.StableBarHomologyComparison

/-!
# 通常の有限 rank の列側半直積の実安定模型

概要：通常の実半直積のブロック安定化を実単体的モノイドの余極限にする。
方針：実一座標遷移と標準包含を順序列に束ねる。
規約：KST Proposition 4.14、SW92 §1.2。H_* の余極限を定義に含めない。
使われ方：実安定相対 bar ホモロジーと有限 rank の実零化の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Opposite
open scoped Simplicial

/-- 概要：通常の単位ブロック和と零埋め列による実半直積の rank 順序列。
方針：実ブロック同変射の全空間写像を一座標遷移とする。
規約：SW92 §1.2。使われ方：実安定列側半直積の定義。 -/
def NonUnitalSimplicialRing.columnAffineRankSequence (I : NonUnitalSimplicialRing.{u}) :
    ℕ ⥤ SimplicialObject MonCat.{u} :=
  Functor.ofSequence (fun n ↦ (I.columnBlockOverHom n 1).total)

/-- 概要：実 ĜL の通常の rank 順序列から列側半直積への実標準包含。
方針：有限 rank の実標準包含と実ブロック対射の正方形を束ねる。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実安定相対項の基準写像。 -/
def NonUnitalSimplicialRing.columnAffineSectionNatTrans (I : NonUnitalSimplicialRing.{u}) :
    I.hatGLRankSequence ⟶ I.columnAffineRankSequence :=
  NatTrans.ofSequence (fun n ↦ simplicialActionProductSection (I.hatGLColumnAction n)) (by
    intro n
    rw [show I.hatGLRankSequence.map (homOfLE (Nat.le_add_right n 1)) = I.hatGLBlockMap n 1 from
      Functor.ofSequence_map_homOfLE_succ _ _,
      show I.columnAffineRankSequence.map (homOfLE (Nat.le_add_right n 1)) =
        (I.columnBlockOverHom n 1).total from Functor.ofSequence_map_homOfLE_succ _ _]
    exact (I.columnBlockOverHom n 1).toPairMap.section_comm.symm)

/-- 概要：通常の列側半直積の実 rank 余極限。
方針：単体的モノイドの実順序余極限を取る。
規約：SW92 §1.2。使われ方：実安定列側アフィン模型。 -/
def NonUnitalSimplicialRing.stableColumnAffine (I : NonUnitalSimplicialRing.{u}) :
    SimplicialObject MonCat.{u} := colimit I.columnAffineRankSequence

/-- 概要：実安定 ĜL の実安定列側半直積への標準包含。
方針：有限 rank の実自然変換を実余極限関手で写す。
規約：KST Proposition 4.14。使われ方：実安定相対 bar ホモロジーの基準。 -/
def NonUnitalSimplicialRing.stableColumnAffineSection (I : NonUnitalSimplicialRing.{u}) :
    I.stableHatGL ⟶ I.stableColumnAffine := colimMap I.columnAffineSectionNatTrans

/-- 概要：列側の実半直積 rank 順序列の右乗法の実自然変換。
方針：実同変射の全空間写像を取り、通常の安定化との実可換性を使う。
規約：SW92 §1.2。使われ方：実安定列側の右乗法。 -/
def NonUnitalSimplicialRing.columnAffineRightNatTrans (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) : I.columnAffineRankSequence ⟶ I.columnAffineRankSequence :=
  NatTrans.ofSequence (fun n ↦ simplicialActionProductMap (I.columnRightActionHom a n)) (by
    intro n
    rw [show I.columnAffineRankSequence.map (homOfLE (Nat.le_add_right n 1)) =
      (I.columnBlockOverHom n 1).total from Functor.ofSequence_map_homOfLE_succ _ _]
    exact (congrArg SimplicialActionPairMap.total (I.columnRight_block_commute a n 1)).symm)

/-- 概要：実安定列側半直積の列に右乗法を施す実写像。
方針：有限 rank の実右乗法の自然変換を実余極限関手に写す。
規約：KST Proposition 4.14。零性は定義に入れない。
使われ方：実安定相対 H_* への誘導。 -/
def NonUnitalSimplicialRing.stableColumnAffineRightMap (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) : I.stableColumnAffine ⟶ I.stableColumnAffine :=
  colimMap (I.columnAffineRightNatTrans a)

end SerrePositivity.KST.ProExcision
