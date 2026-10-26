module

public import SerrePositivity.KST.LocalizingInvariants.SpanConeShape
public import SerrePositivity.KST.LocalizingInvariants.FullSubcomplexFiber
public import SerrePositivity.KST.LocalizingInvariants.FixedMarkedSpanQuasicategory
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeIteratedSliceIso
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexIso

/-!
概要：元の固定端点 marked span を、同じ二終点上の全錐族の全部分複体と同定する。
方針：端点を保つ形状同型を同じ厳密 fiber へ移し、元の実分母条件へ制限する。
規約：左右の実辺を保持する全次数の厳密同型。
使われ方：実分母・次辺族から元の span への比較の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.LocalizingInvariants

/-- 分母条件を課す前の、元の二端点を厳密に固定した span。 -/
def fixedSpanFamily (X : SSet.{u}) (x y : X _⦋0⦌) : SSet.{u} :=
  vertexFiber ((pre spanEndpointInclusion).app X) (functorVertex (intervalMappingBoundary x y))

lemma fixedSpanConeRestriction (X : SSet.{u}) :
    (pre spanBoundaryConeIso.hom).app X ≫ coneRestriction (boundary 1 : SSet.{u}) X =
      (pre spanEndpointInclusion).app X := by
  rw [coneRestriction, ← NatTrans.comp_app, ← pre_map, spanBoundaryConeIso_endpoints]

def spanConePreIso (X : SSet.{u}) : (ihom (horn 2 0 : SSet.{u})).obj X ≅
    (ihom (join (Δ[0] : SSet.{u}) (boundary 1 : SSet.{u}))).obj X where
  hom := (pre spanBoundaryConeIso.hom).app X
  inv := (pre spanBoundaryConeIso.inv).app X
  hom_inv_id := by
    simp only [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id, NatTrans.id_app]
  inv_hom_id := by
    simp only [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id, NatTrans.id_app]

/-- 元の固定端点 span と、同じ二端点の固定図式上の全錐族の厳密同型。 -/
def fixedSpanConeFamilyIso (X : SSet.{u}) (x y : X _⦋0⦌) :
    fixedSpanFamily X x y ≅ coneFamily (intervalMappingBoundary x y) :=
  vertexFiberIsoOfOverIso _ _ (spanConePreIso X)
    (fixedSpanConeRestriction X) _

lemma fixedSpanConeFamilyIso_ι (X : SSet.{u}) (x y : X _⦋0⦌) :
    (fixedSpanConeFamilyIso X x y).hom ≫ vertexFiberι
      (coneRestriction (boundary 1 : SSet.{u}) X) (functorVertex (intervalMappingBoundary x y)) =
      vertexFiberι ((pre spanEndpointInclusion).app X)
        (functorVertex (intervalMappingBoundary x y)) ≫ (pre spanBoundaryConeIso.hom).app X :=
  vertexFiberIsoOfOverIso_hom_ι _ _ _ _ _

/-- 二終点上の錐の形状内の、元の分母に当たる実辺。 -/
def spanConeDenominatorInclusion : (Δ[1] : SSet.{u}) ⟶
    join (Δ[0] : SSet.{u}) (boundary 1 : SSet.{u}) :=
  (joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (boundary.ι (1 : Fin 2))

lemma spanConeDenominatorInclusion_shape :
    spanConeDenominatorInclusion.{u} ≫ spanBoundaryConeIso.hom = horn₂₀.ι₀₁ := by
  rw [spanConeDenominatorInclusion, Category.assoc, spanBoundaryConeIso_left,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 同じ固定二終点の全錐族から、元の左脚の全族を回収する。 -/
def spanConeDenominatorFamily {X : SSet.{u}} (x y : X _⦋0⦌) :
    coneFamily (intervalMappingBoundary x y) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  vertexFiberι (coneRestriction (boundary 1 : SSet.{u}) X)
    (functorVertex (intervalMappingBoundary x y)) ≫ (pre spanConeDenominatorInclusion).app X

lemma fixedSpanConeFamilyIso_denominator (X : SSet.{u}) (x y : X _⦋0⦌) :
    (fixedSpanConeFamilyIso X x y).hom ≫ spanConeDenominatorFamily x y =
      vertexFiberι ((pre spanEndpointInclusion).app X)
        (functorVertex (intervalMappingBoundary x y)) ≫ (pre horn₂₀.ι₀₁).app X := by
  change _ ≫ (_ ≫ (pre spanConeDenominatorInclusion).app X) = _
  rw [← Category.assoc, fixedSpanConeFamilyIso_ι, Category.assoc,
    ← NatTrans.comp_app, ← pre_map, spanConeDenominatorInclusion_shape]

/-- 全錐族に元の左脚の実分母条件を課した全部分複体。 -/
def markedSpanConeFamily {X : SSet.{u}} (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    (coneFamily (intervalMappingBoundary x y)).Subcomplex :=
  fullSubcomplexOnVertices _ (fun v => intervalFunctorVertexEdge
    ((spanConeDenominatorFamily x y).app (Opposite.op ⦋0⦌) v) ∈ W)

instance markedSpanConeFamily_quasicategory {X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    Quasicategory (markedSpanConeFamily W x y : SSet.{u}) := by
  dsimp only [markedSpanConeFamily]
  infer_instance

/-- 元の固定端点 marked span と、同じ実分母条件を持つ全錐族の厳密同型。 -/
def fixedMarkedSpanConeFamilyIso (X : SSet.{u}) (W : Set (X _⦋1⦌))
    (x y : X _⦋0⦌) : fixedMarkedSpans X W x y ≅ (markedSpanConeFamily W x y : SSet.{u}) := by
  let P := fun v : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌ => spanLeftEdge v ∈ W
  let f := (pre spanEndpointInclusion).app X
  let fp := markedSpanBoundary X W
  have hf : fp = (fullSubcomplexOnVertices _ P).ι ≫ f := markedSpanBoundary_restriction X W
  let e := fullSubcomplexFiberIso P f fp hf (functorVertex (intervalMappingBoundary x y))
  refine e ≪≫ fullSubcomplexIso (fixedSpanConeFamilyIso X x y) _ _ ?_
  intro v
  have he := congrArg (fun k => intervalFunctorVertexEdge (k.app (Opposite.op ⦋0⦌) v))
    (fixedSpanConeFamilyIso_denominator X x y)
  change intervalFunctorVertexEdge ((spanConeDenominatorFamily x y).app (Opposite.op ⦋0⦌)
    ((fixedSpanConeFamilyIso X x y).hom.app (Opposite.op ⦋0⦌) v)) = spanLeftEdge v.val at he
  change spanLeftEdge v.val ∈ W ↔ intervalFunctorVertexEdge
    ((spanConeDenominatorFamily x y).app (Opposite.op ⦋0⦌)
      ((fixedSpanConeFamilyIso X x y).hom.app (Opposite.op ⦋0⦌) v)) ∈ W
  rw [he]

end SerrePositivity.KST.LocalizingInvariants
