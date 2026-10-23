module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanConeLowerTriangleFaces
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceTriangleIsoFacesEquality

/-!
概要：全錐円柱の下側三角形の指定ホモトピー類の同型。
方針：元の三辺を指定 Kan 射に揃えて精密化を読む。
規約：元の二単体の値を保持。使われ方：中央・最後の四面の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F G : I ⥤ KanObject.{u}}
  {c : JoinCone (kanDiagramCoherentNerve F)} {d : JoinCone (kanDiagramCoherentNerve G)}
  (T : SSet.Homotopy c.val d.val) (K : KanObject.{u})
  (hc : c.vertex = coherentNerveVertex K)

/-- 概要：元の対角射と脚・図式成分の合成の指定比較。
方針：指定三角形の三辺。規約：元の値。使われ方：内部同型の消去。 -/
def kanConeLowerIso (i : I) :
    FunctorIso (kanConeHomotopyDiagonal T K hc i)
      (kanNativeConeLeg c K hc i ≫ kanConeDiagramComponent T i) :=
  spaceInfinityTriangleIso_of_faces _ _ _
    (coneHomotopyLowerTriangle T (ULift.up (ComposableArrows.mk₀ i)))
    (kanConeLowerTriangle_two T K hc i) (kanConeLowerTriangle_zero T i)
    (kanConeLowerTriangle_one T K hc i)

/-- 概要：指定比較は元の三角形の値と型を含めて等しい。
方針：端点の輸送。規約：同型を選び直さない。使われ方：四面の指定値の同定。 -/
lemma kanConeLowerIso_heq (i : I) :
    HEq (kanConeLowerIso T K hc i) (spaceInfinityTriangleIso
      (coneHomotopyLowerTriangle T (ULift.up (ComposableArrows.mk₀ i)))) :=
  spaceInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
