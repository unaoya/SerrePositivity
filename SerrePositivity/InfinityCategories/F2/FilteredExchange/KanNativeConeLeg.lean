module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.NativeConeLeg
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramCoherentNerve

/-!
概要：𝒮 の native な錐の脚を、指定した Kan 対象間の実際の射へ読み戻す。
方針：頂点の厳密な同定と coherent nerve の辺の全単射。
規約：元の脚の全一単体を保持。使われ方：引き戻し錐の脚と元の Kan 射影の比較。
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

/-- 概要：元の錐の脚を指定された Kan 対象の coherent 辺にする。
方針：両端だけを厳密に同定。規約：全一単体は元のまま。使われ方：脚の読み戻し。 -/
def kanNativeConeLegEdge (i : I) : SpaceInfinity.{u}.Edge
    (coherentNerveVertex K) (coherentNerveVertex (F.obj i)) where
  edge := (nativeConeLeg c (ULift.up (ComposableArrows.mk₀ i))).edge
  src_eq := (nativeConeLeg c _).src_eq.trans hc
  tgt_eq := (nativeConeLeg c _).tgt_eq.trans
    ((kanDiagramCoherentNerve_vertex F i).trans (spaceInfinityVertex_eq_coherent _))

/-- 概要：元の native な脚を実際の Kan 射へ戻す。
方針：指定端点の coherent 辺を逆対応へ送る。規約：元の二対象。使われ方：射影との比較。 -/
def kanNativeConeLeg (i : I) : K ⟶ F.obj i :=
  coherentNerveEdgeToHom (kanNativeConeLegEdge c K hc i)

/-- 概要：読み戻した Kan 射の辺は元の native な脚の全一単体。
方針：coherent nerve の辺と射の往復。規約：厳密な式。使われ方：脚の自然性の読み戻し。 -/
lemma kanNativeConeLeg_edge (i : I) :
    (coherentNerveEdge (kanNativeConeLeg c K hc i)).edge =
      (nativeConeLeg c (ULift.up (ComposableArrows.mk₀ i))).edge := by
  exact congrArg SSet.Edge.edge (coherentNerveEdge_hom (kanNativeConeLegEdge c K hc i))

end SerrePositivity.InfinityCategories.F2
