module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegFiberTransport
public import SerrePositivity.InfinityCategories.F2.Compact.WeakComponents

/-!
概要：弱同値な実 fiber 写像の点を、一つの元の値の pointed fiber から回収する。
方針：同じ全空間の点の射影と、同じ fiber の引き戻し同型を使用する。
規約：底の filtered 性・quasicategory 性は不要。余錐と fiber 写像を変更しない。
使われ方：元の余錐脚の作用による成分の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の全空間の点は、同じ fiber 同型の逆と元の包含により厳密に回収できる。 -/
lemma coconeFiberSource_point {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (e : leftUnstraightening F _⦋0⦌) :
    ∃ b : B _⦋0⦌,
      ∃ w : vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b) _⦋0⦌,
        (coconeLegFiberSource F b).app (Opposite.op ⦋0⦌) w = e := by
  let b := (leftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) e
  let t : vertexFiber (leftUnstraighteningProjection F) b _⦋0⦌ :=
    ⟨e, by rw [pinchedConstant_zero]⟩
  refine ⟨b, (leftUnstraighteningFiberIso F b).hom.app (Opposite.op ⦋0⦌) t, ?_⟩
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (coconeLegFiberSource_hom b)
    (Opposite.op ⦋0⦌)) t

/-- 元の余錐の弱同値な fiber 写像の全成分を、一つの元の値から同じ写像で回収する。 -/
lemma coconeFiber_point_representative_of_weak {B : SSet.{u + 1}}
    {F : B ⟶ SpaceInfinity.{u}} (c : JoinCocone F)
    (hc : IsWeakHomotopyEquivalence (coconeFiberMap c))
    (x : vertexFiber pointedSpaceProjection c.vertex _⦋0⦌) :
    ∃ b : B _⦋0⦌,
      ∃ w : vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b) _⦋0⦌,
        SSet.π₀.mk ((coconeLegFiberMap c b).app (Opposite.op ⦋0⦌) w) = SSet.π₀.mk x := by
  obtain ⟨z, hz⟩ := weakHomotopyEquivalence_mapPiZero_surjective (coconeFiberMap c) hc
    (SSet.π₀.mk x)
  obtain ⟨e, rfl⟩ := SSet.π₀.mk_surjective z
  rw [SSet.mapπ₀_mk] at hz
  obtain ⟨b, w, hw⟩ := coconeFiberSource_point F e
  refine ⟨b, w, ?_⟩
  change SSet.π₀.mk ((coconeFiberMap c).app (Opposite.op ⦋0⦌)
    ((coconeLegFiberSource F b).app (Opposite.op ⦋0⦌) w)) = _
  rw [hw]
  exact hz

end SerrePositivity.InfinityCategories.F2.Compact
