module

public import SerrePositivity.EInfinity.FrameHom.FrameArrowAugmentationLimits
public import SerrePositivity.InfinityCategories.Derived.EvaluationLimitCone
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoConstantEdges
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.F2.CatInfinity.NativeConeLeg

/-!
# 可逆 augmentation の元の極限錐の全脚

概要：同じ全 augmentation を反転する関手の任意の実極限錐の脚を可逆とする。
方針：全錐の同型と指定された全評価ホモトピーの輸送を合成する。
規約：極限対象の同型だけで脚の可逆性を推論しない。
使われ方：実右 Kan 単位の同じ成分の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [Quasicategory E] (F : nerve C ⟶ E)
  (hp : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)

def augmentationLimitConeFunctorIso (hI : IsWeaklyContractible (nerve I))
    (c : JoinCone (nerveMap A ≫ F)) (hc : IsLimitCone c) :
    FunctorIso c.val (SSet.const (F.app (Opposite.op ⦋0⦌) (nerveVertex X))) := by
  let e := augmentationFunctorIso A p F hp
  let t := evaluationLimitConeTransport hI (F.app (Opposite.op ⦋0⦌) (nerveVertex X))
    (FunctorIso.simplicialHomotopy e)
    (fun a => simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) a)
  exact coneFunctorIsoOfVertexIso c t.cone (limitConeIso c t.cone hc t.isLimit) ≪≫
    functorIsoOfPointwiseInvertibleHomotopy t.homotopy t.vertical_isInvertible

include hp in
lemma augmentationLimitCone_leg_isInvertible (hI : IsWeaklyContractible (nerve I))
    (c : JoinCone (nerveMap A ≫ F)) (hc : IsLimitCone c) (i : (nerve I) _⦋0⦌) :
    IsInvertibleEdge (F2.nativeConeLeg c i) := by
  have h := functorIso_const_map_isInvertible _
    (augmentationLimitConeFunctorIso A p F hp hI c hc) (F2.coneDomainLeg i)
  exact (isInvertibleEdge_congr (e := F2.nativeConeLeg c i)
    (f := (F2.coneDomainLeg i).map ((truncation 2).map c.val)) rfl).mpr h

end SerrePositivity.EInfinity.FrameHom.FrameArrows
