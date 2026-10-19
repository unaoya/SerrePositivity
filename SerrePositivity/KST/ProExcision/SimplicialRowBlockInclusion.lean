module
public import SerrePositivity.KST.ProExcision.IdealRowBlockInclusion
public import SerrePositivity.KST.ProExcision.RowAffineSection
public import SerrePositivity.KST.ProExcision.SimplicialColumnBlockInclusion

/-!
# 行側半直積の通常の有限 rank 安定化

概要：単位ブロック和と零埋め行を行側半直積の実単体射にする。
方針：反対 ĜL の作用に対する実同変性を用いて実半直積射を作る。
規約：KST Proposition 4.14、SW92 §1.2。指定元の乗法は含めない。
使われ方：実行側の有限 rank 余極限と列側との比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite

/-- 概要：行側の基底ブロック和と零埋め行による実同変射。
方針：右行列作用に対する零埋めの実同変性を ĜL へ制限する。
規約：SW92 §1.2。使われ方：通常の行側半直積安定化。 -/
def NonUnitalSimplicialRing.rowBlockOverHom (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    SimplicialActionOverHom (I.hatGLRowAction n) (I.hatGLRowAction (n + m)) where
  base := Functor.whiskerRight (I.hatGLBlockMap n m) monCatOpposite
  fiber := I.standardIdeal.columnBlockMap n m
  equivariant k g v := (idealRowBlockInclusion_equivariant (I.standardIdeal.ideal k) n m
    (MulOpposite.unop g).val v).symm

/-- 概要：行側半直積の単位ブロック和と零埋めによる実単体射。
方針：実同変射の実半直積写像の乗法を反転する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：通常の有限 rank 遷移。 -/
def NonUnitalSimplicialRing.rowAffineBlockMap (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    I.rowAffine n ⟶ I.rowAffine (n + m) :=
  Functor.whiskerRight (I.rowBlockOverHom n m).total monCatOpposite

/-- 概要：実行側のブロック安定化は標準の基底包含と可換。
方針：実写像を各次数で評価し、零埋めの単位元保存を用いる。
規約：SW92 §1.2。使われ方：実行側相対安定化の降下。 -/
lemma NonUnitalSimplicialRing.rowAffineBlockMap_section
    (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    I.rowAffineSection n ≫ I.rowAffineBlockMap n m =
      I.hatGLBlockMap n m ≫ I.rowAffineSection (n + m) := by
  apply NatTrans.ext
  funext k
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro g
  apply MulOpposite.unop_injective
  apply ActionProduct.ext
  · rfl
  · exact map_one (columnBlockInclusion (I.standardIdeal.ideal k) n m).toMultiplicative

end SerrePositivity.KST.ProExcision
