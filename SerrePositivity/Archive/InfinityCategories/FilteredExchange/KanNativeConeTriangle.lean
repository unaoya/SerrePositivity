module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanNativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeTriangle
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceTriangleFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CosliceTransport

/-!
概要：通常の Kan 図式上の native 錐の指定三角形を元の射のホモトピーへ戻す。
方針：元の join 二単体の三辺を同定し、その精密化を uncurry する。
規約：新しい充填や代表を選ばない。使われ方：引き戻し錐の指定可換性の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F : I ⥤ KanObject.{u}}
  (c : JoinCone (kanDiagramCoherentNerve F)) (K : KanObject.{u})
  (hc : c.vertex = coherentNerveVertex K)

/-- 概要：形状の元の射上の native 錐の指定二単体。
方針：join の標準三角形で制限。規約：元の全単体。使われ方：脚の可換性。 -/
def kanNativeConeTriangle {i j : I} (f : i ⟶ j) : SpaceInfinity.{u} _⦋2⦌ :=
  nativeConeTriangle c (ULift.up (nerve.edgeMk f).edge)

/-- 概要：指定三角形の底辺は元の図式の射。
方針：native な面と strict 図式を照合。規約：厳密な式。使われ方：三辺の同定。 -/
lemma kanNativeConeTriangle_zero {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (kanNativeConeTriangle c f) = (coherentNerveEdge (F.map f)).edge := by
  rw [kanNativeConeTriangle, nativeConeTriangle_zero]
  exact strictCoherentDiagram_edge F f

/-- 概要：指定三角形の長辺は終域への元の脚。
方針：底辺の終点と辺の往復を照合。規約：元の一単体。使われ方：指定円柱の終点。 -/
lemma kanNativeConeTriangle_one {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (kanNativeConeTriangle c f) =
      (coherentNerveEdge (kanNativeConeLeg c K hc j)).edge := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve I)
  have hk : J.δ 0 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ j) := by
    apply ULift.ext
    exact (nerve.edgeMk f).tgt_eq
  have h := nativeConeTriangle_face c (ULift.up (nerve.edgeMk f).edge) (0 : Fin 2)
  exact h.trans ((congrArg (fun k : J _⦋0⦌ ↦ (nativeConeLeg c k).edge) hk).trans
    (kanNativeConeLeg_edge c K hc j).symm)

/-- 概要：指定三角形の最初の辺は始域への元の脚。
方針：底辺の始点と辺の往復を照合。規約：元の一単体。使われ方：指定円柱の始点。 -/
lemma kanNativeConeTriangle_two {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 2 (kanNativeConeTriangle c f) =
      (coherentNerveEdge (kanNativeConeLeg c K hc i)).edge := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve I)
  have hk : J.δ 1 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ i) := by
    apply ULift.ext
    exact (nerve.edgeMk f).src_eq
  have h := nativeConeTriangle_face c (ULift.up (nerve.edgeMk f).edge) (1 : Fin 2)
  exact h.trans ((congrArg (fun k : J _⦋0⦌ ↦ (nativeConeLeg c k).edge) hk).trans
    (kanNativeConeLeg_edge c K hc i).symm)

/-- 概要：native な三角形そのものから元の Kan 射間の指定ホモトピーを得る。
方針：三辺の厳密な同定と精密化の uncurry。規約：元の二単体。使われ方：錐の整合。 -/
def kanNativeConeTriangleHomotopy {i j : I} (f : i ⟶ j) :
    SSet.Homotopy (kanNativeConeLeg c K hc j) (kanNativeConeLeg c K hc i ≫ F.map f) :=
  spaceInfinityTriangleHomotopy_of_faces _ _ _ (kanNativeConeTriangle c f)
    (kanNativeConeTriangle_two c K hc f) (kanNativeConeTriangle_zero c f)
    (kanNativeConeTriangle_one c K hc f)

end SerrePositivity.InfinityCategories.F2
