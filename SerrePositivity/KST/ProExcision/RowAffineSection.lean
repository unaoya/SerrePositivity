module
public import SerrePositivity.KST.ProExcision.ColumnRowAffineIso

/-!
# 行側半直積の標準包含と実反対転置の整合

概要：行成分を零とする ĜL の実包含と列側の実比較の可換性を証明する。
方針：基底は反対転置、行成分は実乗法同型の単位元保存を使う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実相対 bar 同型の定義。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite

/-- 概要：実行側半直積への ĜL の標準包含。
方針：反対 ĜL を基底に置き、行成分を単位元にして反対半直積へ移す。
規約：SW92 §1.2、行ベクトルの加法表記では零。
使われ方：実行側相対ホモロジーの基準射。 -/
def NonUnitalSimplicialRing.rowAffineSection (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    I.hatGL n ⟶ I.rowAffine n where
  app k := by
    letI := (I.hatGLRowAction n).actionStructure k
    exact MonCat.ofHom {
      toFun g := MulOpposite.op ⟨MulOpposite.op g, 1⟩
      map_one' := rfl
      map_mul' g h := by
        apply MulOpposite.unop_injective
        apply ActionProduct.ext
        · rfl
        · change 1 = 1 * ((I.hatGLRowAction n).action k (MulOpposite.op h) 1)
          rw [map_one, one_mul] }
  naturality {k l} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply MulOpposite.unop_injective
    apply ActionProduct.ext
    · rfl
    · exact ((I.standardIdeal.columnGroup n ⋙ forget₂ GrpCat MonCat).map f).hom.map_one.symm

/-- 概要：列側と行側の実比較は基底の標準包含と可換。
方針：二重反対型を外し、ファイバーの単位元保存を使う。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：相対加群への実同型の降下。 -/
lemma NonUnitalSimplicialRing.reverseOppositeAffineIso_section
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    simplicialActionProductSection (I.reverseOpposite.hatGLColumnAction n) ≫
        (I.reverseOppositeAffineIso n).hom =
      (I.reverseOppositeHatGLIso n).hom ≫ monoidReverseOppositeMap (I.rowAffineSection n) := by
  apply NatTrans.ext
  funext k
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro g
  apply MulOpposite.unop_injective
  apply MulOpposite.unop_injective
  apply ActionProduct.ext
  · rfl
  · exact map_one (integerUnitizationIdealOpVectorMulEquiv (I.obj k) n)

end SerrePositivity.KST.ProExcision
