module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceMappingSpaces

/-!
概要：pointed-space 射影と left unstraightening の fiber による空間値の回収。
方針：左写像空間を右写像空間へ移し、coherent Hom 比較と一点からの豊穣 Hom を使う。
規約：値の Kan 複体の宇宙は fiber と同じ u+1 に持ち上げる。
使われ方：Kerodon Construction 5.5.2.1、Example 5.6.2.9、空間値 unstraightening の fiber 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：pointed-space 射影の fiber は、その底の頂点が表す Kan 複体と同値。
方針：fiber の左写像空間表示、左右の比較、coherent Hom の値の回収を合成する。
規約：比較先だけを u+1 に持ち上げ、𝒮 の極限は用いない。
使われ方：Kerodon Construction 5.5.2.1、普遍的な left fibration の fiber。 -/
noncomputable def pointedSpaceFiberValueEquivalence (s : SpaceInfinity.{u} _⦋0⦌) :
    QCatEquivalence (vertexFiber pointedSpaceProjection s)
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject s).obj) :=
  (qCatEquivalenceOfIso (pointedSpaceFiberPinchedLeftIso s)).trans
    ((pinchedHomLeftRightEquivalence pointSpaceVertex s).trans
      (pointSpaceRightMappingEquivalenceAt s))

/-- 概要：left unstraightening の fiber は対応する図式の空間値と同値。
方針：引き戻しの fiber の同型に続けて、普遍的な pointed-space fiber の値を回収する。
規約：底 C に quasicategory 性は要求せず、値は u+1 に持ち上げる。
使われ方：Kerodon Example 5.6.2.9、straightening の値を fiber で確認する定理。 -/
noncomputable def leftUnstraighteningFiberValueEquivalence {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    QCatEquivalence (vertexFiber (leftUnstraighteningProjection F) c)
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) c)).obj) :=
  (qCatEquivalenceOfIso (leftUnstraighteningFiberIso F c)).trans
    (pointedSpaceFiberValueEquivalence (F.app (Opposite.op ⦋0⦌) c))

end SerrePositivity.InfinityCategories
