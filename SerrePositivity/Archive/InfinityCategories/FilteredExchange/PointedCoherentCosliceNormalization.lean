module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoslicePostCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices

/-!
概要：coherent な一点頂点の coslice 全体を、元の pointed-space 表示へ移す。
方針：既存の一点頂点の等式から厳密な同型を作り、元の射影と錐を保持する。
規約：同じ底の全単体を保持。使われ方：全 Hom 族を実 pointed 族に戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 一点頂点の表示変更による、coslice 全体と実 pointed space の厳密な同型。 -/
def pointedCoherentCosliceIso :
    sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex pointKanObject.{u})) ≅
      PointedSpaceInfinity.{u} :=
  eqToIso (congrArg (fun v => sliceUnder (SSet.yonedaEquiv.symm v))
    (spaceInfinityVertex_eq_coherent pointKanObject).symm)

/-- 同じ厳密な同型は、全 coslice 上で元の射影を保つ。 -/
lemma pointedCoherentCosliceIso_projection :
    pointedCoherentCosliceIso.hom ≫ pointedSpaceProjection =
      sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex pointKanObject.{u})) :=
  sliceUnder_eqToHom_projection
    (congrArg SSet.yonedaEquiv.symm (spaceInfinityVertex_eq_coherent pointKanObject).symm)

/-- 表示変更は任意の次数で元の錐の射を一切変更しない。 -/
lemma pointedCoherentCosliceIso_app_val {n : ℕ}
    (a : (sliceUnder (SSet.yonedaEquiv.symm
      (coherentNerveVertex pointKanObject.{u}))) _⦋n⦌) :
    (pointedCoherentCosliceIso.hom.app (Opposite.op ⦋n⦌) a).val = a.val :=
  sliceUnder_eqToHom_app_val
    (congrArg SSet.yonedaEquiv.symm (spaceInfinityVertex_eq_coherent pointKanObject).symm) n a

end SerrePositivity.InfinityCategories.F2
