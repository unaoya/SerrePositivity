module
public import SerrePositivity.KST.ProExcision.BlockStabilizationCoherence

/-!
# 通常の列のブロック安定化の実対射の合成則

概要：補助 rank 零の対射と、一座標ずつ増やす合成を同定する。
方針：基底・全空間の実射をそれぞれの成分で比較する。
規約：KST Claim 4.15 から Proposition 4.14 の順序余極限への移送。
使われ方：相対加群の実順序列の遷移の計算。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {G H G' H' : SimplicialObject MonCat.{u}}

/-- 概要：半直積対の射は基底射と全空間射で決まる。
方針：可換性の証明の proof irrelevance を使う。
規約：KST Proposition 4.14。使われ方：rank の対射の合成則。 -/
lemma SimplicialActionPairMap.ext_of_maps {A : SimplicialMonoidAction G H}
    {B : SimplicialMonoidAction G' H'} {f g : SimplicialActionPairMap A B}
    (hb : f.base = g.base) (ht : f.total = g.total) : f = g := by
  cases f
  cases g
  cases hb
  cases ht
  rfl

/-- 概要：半直積対の恒等射。
方針：二つの射を恒等射とする。
規約：KST Proposition 4.14。使われ方：補助 rank 零の対射との同定。 -/
def SimplicialActionPairMap.identity (A : SimplicialMonoidAction G H) : SimplicialActionPairMap A A where
  base := 𝟙 _
  total := 𝟙 _
  section_comm := by simp

/-- 概要：補助 rank 零の通常の列のブロック対射は恒等。
方針：基底のブロック和と列の零埋めを別々に計算する。
規約：KST Proposition 4.14。使われ方：反復安定化の基底。 -/
lemma NonUnitalSimplicialRing.columnBlockPair_zero (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    (I.columnBlockOverHom n 0).toPairMap = SimplicialActionPairMap.identity (I.hatGLColumnAction n) := by
  apply SimplicialActionPairMap.ext_of_maps
  · apply NatTrans.ext
    funext k
    rcases k with ⟨⟨q⟩⟩
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro M
    apply Subtype.ext
    exact firstBlockMatrix_zero n M.val
  · apply NatTrans.ext
    funext k
    letI := (I.hatGLColumnAction n).actionStructure k
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply ActionProduct.ext
    · apply Subtype.ext
      exact firstBlockMatrix_zero n x.base.val
    · exact columnBlockInclusion_zero _ n x.fiber.toAdd

/-- 概要：列のブロック対射を一座標安定化すると補助 rank を一つ増やした対射に一致する。
方針：二つの成分の合成則を基底射と全空間射へ適用する。
規約：KST Proposition 4.14。使われ方：実順序列の任意の有限遷移の計算。 -/
lemma NonUnitalSimplicialRing.columnBlockPair_succ (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    ((I.columnBlockOverHom n m).toPairMap).comp ((I.columnBlockOverHom (n + m) 1).toPairMap) =
      (I.columnBlockOverHom n (m + 1)).toPairMap := by
  apply SimplicialActionPairMap.ext_of_maps
  · apply NatTrans.ext
    funext k
    rcases k with ⟨⟨q⟩⟩
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro M
    apply Subtype.ext
    exact firstBlockMatrix_succ n m M.val
  · apply NatTrans.ext
    funext k
    letI := (I.hatGLColumnAction n).actionStructure k
    letI := (I.hatGLColumnAction (n + m)).actionStructure k
    letI := (I.hatGLColumnAction (n + m + 1)).actionStructure k
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply ActionProduct.ext
    · apply Subtype.ext
      exact firstBlockMatrix_succ n m x.base.val
    · exact columnBlockInclusion_succ _ n m x.fiber.toAdd

end SerrePositivity.KST.ProExcision
