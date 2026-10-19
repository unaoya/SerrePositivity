module
public import SerrePositivity.KST.ProExcision.RowAffineSection
public import SerrePositivity.KST.ProExcision.IdealLeftMultiplication
public import SerrePositivity.KST.ProExcision.NonUnitalVertexReverse

/-!
# 行側半直積の左乗法による実単体的自己射

概要：零次の指定元による行の左乗法を行側半直積の実写像にする。
方針：右行列作用との実同変性と係数自然性を各次数で使う。
規約：KST Proposition 4.14、SW92 §1.2。中心性も単射性もこの構成には不要。
使われ方：反対係数の列の右乗法の零化を行側へ移す値域。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：実単体的イデアルの行群への指定元による左乗法。
方針：全次数の指定元と実係数自然性から実自然変換を作る。
規約：SW92 §1.2。使われ方：行側同変射のファイバー写像。 -/
def SimplicialIdealData.rowLeftMap (I : SimplicialIdealData.{u})
    (a : I.ideal (op ⦋0⦌)) (n : ℕ) :
    I.columnGroup n ⋙ forget₂ GrpCat MonCat ⟶ I.columnGroup n ⋙ forget₂ GrpCat MonCat where
  app k := MonCat.ofHom (idealVectorLeftHom (I.ideal k) (Fin n) (I.vertexElement a k).val)
  naturality {k l} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro v
    exact (idealVectorLeftHom_functorial (I.ideal k) (I.ideal l) (Fin n) (I.ambient.map f).hom
      (I.map_mem f) (I.vertexElement a k).val (I.vertexElement a l).val
      (I.vertexElement_natural a f) v).symm

/-- 概要：行の左乗法は反対 ĜL の右行列作用に同変。
方針：全行列に対する実同変性を実 ĜL の表現へ制限する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実半直積誘導写像。 -/
def NonUnitalSimplicialRing.rowLeftActionHom (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n : ℕ) :
    SimplicialActionHom (I.hatGLRowAction n) (I.hatGLRowAction n) where
  hom := I.standardIdeal.rowLeftMap (I.standardElement a) n
  equivariant k g v := by
    exact idealVectorLeftHom_equivariant n _ _
      (MulOpposite.op (MulOpposite.unop g).val) v

/-- 概要：行側半直積の行成分に左乗法を施す実単体的自己射。
方針：実同変射の半直積写像の乗法方向を反転する。
規約：SW92 §1.2、基底は恒等。使われ方：実行側相対写像の構成。 -/
def NonUnitalSimplicialRing.rowAffineLeftMap (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n : ℕ) : I.rowAffine n ⟶ I.rowAffine n :=
  Functor.whiskerRight (simplicialActionProductMap (I.rowLeftActionHom a n)) monCatOpposite

/-- 概要：行側の左乗法は標準の ĜL 包含を固定する。
方針：行成分の零の保存を各次数で使う。
規約：KST Proposition 4.14。使われ方：実相対加群写像への降下。 -/
lemma NonUnitalSimplicialRing.rowAffineLeftMap_section (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n : ℕ) :
    I.rowAffineSection n ≫ I.rowAffineLeftMap a n = I.rowAffineSection n := by
  apply NatTrans.ext
  funext k
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro g
  apply MulOpposite.unop_injective
  apply ActionProduct.ext
  · rfl
  · exact map_one (idealVectorLeftHom (I.standardIdeal.ideal k) (Fin n)
      (I.standardIdeal.vertexElement (I.standardElement a) k).val)

end SerrePositivity.KST.ProExcision
