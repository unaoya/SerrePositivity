module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointReconstructedFace
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の終点 slice 比較を、同じ実 comma の二射影の表示へそろえる。
方針：元の両端の全写像の等号だけで指定同型を移送する。
規約：元の比較の指定値と両全族を保持する。
使われ方：元の充満忠実な逆像の指定値を、旧族で厳密に回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
  (V : IndConeExtendedSliceData κ D q G)
/-- 概要：元の終点 slice 比較を、同じ実 comma の元の二射影の表示へそろえる。
方針：元の両端の等号だけで表示変更。規約：指定値を保持。使われ方：実 comma の反映。 -/
def indConeEndpointAlignedSliceIso : FunctorIso
    (indConeEndpointRawFace V ≫
      pullback.snd (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)))
    (indConeEndpointReconstructedRawFace V ≫
      pullback.snd (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D))) :=
  F2.functorIsoOfEq (indConeEndpointSliceFunctorIso V) (indConeEndpointSliceCone_source V)
    (indConeEndpointReconstructedRawFace_slice V).symm
/-- 概要：元の二射影の表示へ移しても、元の同じ全 slice 比較の指定値を保持する。
方針：両端の等号の移送。規約：同じ指定値。使われ方：旧族の比較の相対反映。 -/
lemma indConeEndpointAlignedSliceIso_heq :
    HEq (indConeEndpointAlignedSliceIso V) (indConeEndpointSliceFunctorIso V) :=
  F2.functorIsoOfEq_heq _ _ _
end SerrePositivity.InfinityCategories.F2.Ind
