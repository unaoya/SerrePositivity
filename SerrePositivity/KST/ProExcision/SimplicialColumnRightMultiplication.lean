module
public import SerrePositivity.KST.ProExcision.SimplicialColumnBlockInclusion

/-!
# 同じ rank の列の右乗法の実単体射

概要：単体的イデアルの指定元による列の右乗法を単体的に構成する。
方針：指定元の面・退化との自然性と係数準同型による右乗法の自然性を使う。
規約：KST Proposition 4.14 の (id,a)、非可換な係数で左行列作用と可換。
使われ方：安定相対項の右乗法の有限 rank の成分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：列群の右乗法の実単体射。
方針：各次数の指定元を使い、係数写像による右乗法の自然性を適用する。
規約：KST Proposition 4.14 の列側の a 倍。使われ方：同じ rank の半直積の自己射。 -/
def SimplicialIdealData.columnRightMap (I : SimplicialIdealData.{u})
    (a : I.ideal (op ⦋0⦌)) (n : ℕ) :
    I.columnGroup n ⋙ forget₂ GrpCat MonCat ⟶ I.columnGroup n ⋙ forget₂ GrpCat MonCat where
  app k := MonCat.ofHom (idealVectorRightHom (I.ideal k) (Fin n) (I.vertexElement a k).val)
  naturality {k l} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro v
    exact idealVectorRightHom_functorial (I.ideal k) (I.ideal l) (Fin n) (I.ambient.map f).hom
      (I.map_mem f) (I.vertexElement a k).val (I.vertexElement a l).val (I.vertexElement_natural a f) v

/-- 概要：非単位環の ĜL 作用の下で列の右乗法は同変。
方針：全行列の左作用と右乗法の結合律による可換性を制限する。
規約：KST Proposition 4.14、a の中心性はこの同変性に不要。
使われ方：安定相対項の (id,a) 写像。 -/
def NonUnitalSimplicialRing.columnRightActionHom (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n : ℕ) :
    SimplicialActionHom (I.hatGLColumnAction n) (I.hatGLColumnAction n) where
  hom := I.standardIdeal.columnRightMap (I.standardElement a) n
  equivariant k g v := by
    rcases k with ⟨⟨q⟩⟩
    exact idealVectorRightHom_equivariant n _ _ g.val v

end SerrePositivity.KST.ProExcision
