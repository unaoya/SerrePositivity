module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PinchedHomIso
public import SerrePositivity.InfinityCategories.F1.Coherent.FlagIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentLeftHomComparison

/-!
概要：coherent nerve の左 pinched 写像空間を旗の解像の反転で厳密に表示する。
方針：反転した nerve の右 Hom を反対の単体的圏へ移し、既存の旗の表示を反転する。
規約：比較の逆を同値から選ばず、単体集合の同型を使う。
使われ方：Kerodon Proposition 4.6.7.16、Corollary 5.6.0.6、左 coslice fiber の自然な解像模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：反転した coherent nerve の右 Hom は反対圏の coherent nerve の対応する Hom と同型。
方針：nerve の反対の同型を Hom に作用させ、二端点を標準頂点へ正規化する。
規約：二端点は y、x の順。
使われ方：Kerodon §4.6.7、左 Hom の旗の表示への反転前の移送。 -/
noncomputable def coherentOppositePinchedIso {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (x y : C) :
    pinchedHom (X := (SimplicialNerve C).op)
      (SSet.opObjEquiv.symm (coherentNerveVertex y))
      (SSet.opObjEquiv.symm (coherentNerveVertex x)) ≅
    pinchedHom (coherentNerveVertex (Opposite.op y)) (coherentNerveVertex (Opposite.op x)) :=
  pinchedHomIsoOfIso (HomotopyLimits.coherentNerveOppositeIso C)
      (SSet.opObjEquiv.symm (coherentNerveVertex y))
      (SSet.opObjEquiv.symm (coherentNerveVertex x)) ≪≫
    eqToIso (congrArg₂ (fun a b ↦ pinchedHom a b)
      (HomotopyLimits.coherentNerveOppositeMap_vertex y)
      (HomotopyLimits.coherentNerveOppositeMap_vertex x))

/-- 概要：左 pinched 写像空間は豊穣 Hom の旗の解像の反転を持ち上げたものと同型。
方針：反転前の右 Hom を反対圏へ移し、旗の表示を反転して ULift と反転を交換する。
規約：豊穣 Hom の宇宙 u、coherent nerve の宇宙 max(u,v) を明示する。
使われ方：Kerodon Proposition 4.6.7.16、Corollary 5.6.0.6、左 coslice fiber の具体的な座標模型。 -/
noncomputable def coherentLeftPinchedFlagIso {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (x y : C) :
    pinchedHomLeft (coherentNerveVertex x) (coherentNerveVertex y) ≅
      (SSet.uliftFunctor.{v, u}).obj
        (coherentResolutionRightAdjoint.obj (SimplicialCategory.sHom x y)).op :=
  SSet.opFunctor.mapIso
      (coherentOppositePinchedIso x y ≪≫ coherentPinchedFlagIso (Opposite.op y) (Opposite.op x)) ≪≫
    (HomotopyLimits.uliftOppositeIso
      (coherentResolutionRightAdjoint.obj (SimplicialCategory.sHom x y))).symm

end SerrePositivity.InfinityCategories
