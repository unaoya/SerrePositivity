module
public import SerrePositivity.KST.ProExcision.TriangularAffineSplit

/-!
# 単体的な三角ブロック群の実半直積への分解

概要：左上ブロックと最終列の実分解を係数方向に自然に束ねる。
方針：各成分の係数写像と実分解の定義を比較する。
規約：KST Claim 4.15、単体的な非可換イデアル模型。
使われ方：Lemma 4.16 の bar 比較から実半直積の bar 比較への後合成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：実三角群の列作用を単体的に構成する。
方針：実行列の値と列の係数写像に対する全行列作用の自然性を使う。
規約：KST Claim 4.15 の三角群と列群の半直積。
使われ方：実分解の単体的な値域。 -/
def SimplicialIdealData.triangularColumnAction (I : SimplicialIdealData.{u}) (n m : ℕ) :
    SimplicialMonoidAction (I.triangularGroup n m ⋙ forget₂ GrpCat MonCat)
      (I.columnGroup (n + m) ⋙ forget₂ GrpCat MonCat) where
  action k := SerrePositivity.KST.ProExcision.triangularColumnAction n m (I.ideal k)
  naturality {k l} f g v := idealMatrixAction_functorial (n + m) (I.ideal k) (I.ideal l)
    (I.ambient.map f).hom (I.map_mem f) g.val.val v

/-- 概要：三角群の実半直積への分解は単体的。
方針：基底の左上ブロックとファイバーの最終列について係数写像との可換性を確認する。
規約：KST Claim 4.15、実単体的モノイドの間の自然変換。
使われ方：右乗法の実ホモトピーの値域の相対 bar 比較。 -/
def SimplicialIdealData.triangularAffineSplitMap (I : SimplicialIdealData.{u}) (n m : ℕ) :
    I.triangularGroup n (m + 1) ⋙ forget₂ GrpCat MonCat ⟶
      simplicialActionProduct (I.triangularColumnAction n m) where
  app k := by
    letI := (I.triangularColumnAction n m).actionStructure k
    exact MonCat.ofHom (triangularBlockAffineSplit n m (I.ideal k))
  naturality {k l} f := by
    letI := (I.triangularColumnAction n m).actionStructure k
    letI := (I.triangularColumnAction n m).actionStructure l
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply ActionProduct.ext
    · apply Subtype.ext
      apply Units.ext
      rfl
    · rfl

end SerrePositivity.KST.ProExcision
