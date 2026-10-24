module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionIsoNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedDiagonalInputPair
/-!
概要：矢印 Hom と二合成対角の同型が二つの元可変辺を保持することを示す。
方針：二つの標準三角形の可変辺を回収し、同じ順序の対へまとめる。
規約：始側入力を第一成分、終側入力を第二成分に置く。
使われ方：主標的の全区間 Hom を同じ二入力付き四座標へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X T : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)

def dgGluingArrowCompositionEndpointPair :
    dgGluingArrowCompositionPullback f g ⟶ intervalMappingSpace a c ⊗ intervalMappingSpace b d :=
  dgGluingRestrictedDiagonalEndpointPair (compositionCorrespondenceFirst a g)
    (dgGluingFirstFixedCompositionSecond f d) (compositionCorrespondenceDiagonal a g)
    (dgGluingFirstFixedCompositionDiagonal f d)

lemma dgGluingArrowCompositionIso_inv_endpoints
    (h : T ⟶ intervalMappingSpace (functorVertex (SSet.yonedaEquiv.symm f.edge))
      (functorVertex (SSet.yonedaEquiv.symm g.edge))) :
    h ≫ (dgGluingArrowCompositionIso f g).inv ≫ dgGluingArrowCompositionEndpointPair f g =
      lift (dgGluingArrowHomSourceComponent f g h) (dgGluingArrowHomTargetComponent f g h) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [dgGluingArrowCompositionEndpointPair, dgGluingRestrictedDiagonalEndpointPair,
      Category.assoc, lift_fst]
    rw [reassoc_of% dgGluingArrowCompositionIso_inv_last f g h,
      dgGluingArrowHomLastComposition, dgGluingLastFixedCompositionLift_first]
  · simp only [dgGluingArrowCompositionEndpointPair, dgGluingRestrictedDiagonalEndpointPair,
      Category.assoc, lift_snd]
    rw [reassoc_of% dgGluingArrowCompositionIso_inv_first f g h,
      dgGluingArrowHomFirstComposition, dgGluingFirstFixedCompositionLift_second]
end SerrePositivity.InfinityCategories
