module
public import SerrePositivity.KST.ProExcision.NonUnitalHatGLMaps
public import SerrePositivity.KST.ProExcision.SimplicialRowAffine
public import SerrePositivity.KST.ProExcision.ActionOverMorphisms

/-!
# 非単位単体環の実係数射による行・列アフィン写像

概要：実係数変更を実核イデアルの行・列群と実 ĜL 作用に誘導する。
方針：実単位化係数射の自然性と既証明の実行列作用の係数自然性を用いる。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実 aI→I のアフィン包含。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
variable {I J : NonUnitalSimplicialRing.{u}}

/-- 概要：実非単位単体環射による実核イデアル内のベクトル群の係数変更。
方針：各次数の実イデアル係数射を実単位化の自然性で束ねる。
規約：KST Proposition 4.14。使われ方：行・列の実アフィン包含のファイバー射。 -/
def NonUnitalSimplicialRingHom.columnGroupMap (f : NonUnitalSimplicialRingHom I J) (n : ℕ) :
    I.standardIdeal.columnGroup n ⋙ forget₂ GrpCat MonCat ⟶
      J.standardIdeal.columnGroup n ⋙ forget₂ GrpCat MonCat where
  app k := MonCat.ofHom (idealVectorMap (I.standardIdeal.ideal k) (J.standardIdeal.ideal k)
    (Fin n) (integerUnitizationMap (f.app k)) (integerUnitizationMap_ideal (f.app k)))
  naturality {k l} φ := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro v
    change (fun i ↦ idealCoefficientAddHom _ _ (integerUnitizationMap (f.app l))
        (integerUnitizationMap_ideal (f.app l))
        (idealCoefficientAddHom _ _ (I.standardIdeal.ambient.map φ).hom
          (I.standardIdeal.map_mem φ) (v.toAdd i))) =
      (fun i ↦ idealCoefficientAddHom _ _ (J.standardIdeal.ambient.map φ).hom
        (J.standardIdeal.map_mem φ) (idealCoefficientAddHom _ _ (integerUnitizationMap (f.app k))
          (integerUnitizationMap_ideal (f.app k)) (v.toAdd i)))
    funext i
    apply Subtype.ext
    exact congrArg (fun h : I.standardIdeal.ambient.obj k ⟶ J.standardIdeal.ambient.obj l ↦
      h.hom (v.toAdd i).val) (f.unitizationMap.naturality φ)

/-- 概要：実係数射は実 ĜL の列作用に同変な実射を与える。
方針：実 ĜL と実核イデアルの係数射に全行列作用の実自然性を適用する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：実係数イデアルの列側相対包含。 -/
def NonUnitalSimplicialRingHom.columnActionOverHom (f : NonUnitalSimplicialRingHom I J) (n : ℕ) :
    SimplicialActionOverHom (I.hatGLColumnAction n) (J.hatGLColumnAction n) where
  base := f.hatGLMap n
  fiber := f.columnGroupMap n
  equivariant k g v := idealMatrixAction_functorial n (I.standardIdeal.ideal k)
    (J.standardIdeal.ideal k) (integerUnitizationMap (f.app k))
    (integerUnitizationMap_ideal (f.app k)) g.val v

/-- 概要：実係数射は実反対 ĜL の行作用に同変な実射を与える。
方針：実反対 ĜL と実核イデアルの係数射に右行列作用の実自然性を適用する。
規約：SW92 §1.2、非可換係数。
使われ方：実係数イデアルの行側相対包含。 -/
def NonUnitalSimplicialRingHom.rowActionOverHom (f : NonUnitalSimplicialRingHom I J) (n : ℕ) :
    SimplicialActionOverHom (I.hatGLRowAction n) (J.hatGLRowAction n) where
  base := Functor.whiskerRight (f.hatGLMap n) monCatOpposite
  fiber := f.columnGroupMap n
  equivariant k g v := idealRowMatrixAction_functorial n (I.standardIdeal.ideal k)
    (J.standardIdeal.ideal k) (integerUnitizationMap (f.app k))
    (integerUnitizationMap_ideal (f.app k)) (MulOpposite.op (MulOpposite.unop g).val) v

end SerrePositivity.KST.ProExcision
