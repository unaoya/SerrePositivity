module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceOld
public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceBoundaryNaturality

/-!
概要：再構成した終点面の全余錐と底余錐を、元の旧族の同じ全余錐へ厳密に戻す。
方針：元の円柱全体を固定する等号を、同じ終点で制限する。
規約：元の旧族と下方余錐の入力を保持する。
使われ方：終点比較の旧族への制限が、拡張の選び方で変わらないことの確認。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
  (V : IndConeExtendedSliceData κ D q G)
/-- 概要：元の終点面の指定比較は、任意の元の点の同じ境界比較そのもの。
方針：元の定義を照合。規約：指定値の等号。使われ方：元の極大点評価の比較の制限。 -/
lemma indConeEndpointSliceFunctorIso_eq :
    indConeEndpointSliceFunctorIso V =
    conePointSliceBoundaryFunctorIso (indConeEndpointPoint κ D) (indConeEndpointBaseCone V)
      (indConeEndpointBaseCone_tip V) (indConeEndpointSliceCone V) rfl
      (indConeEndpointSliceCone_tip_uncurry V) := rfl
/-- 概要：元の終点面の比較を旧族で制限すると、同じ制限余錐の指定比較を回収する。
方針：同じ点の元の比較の自然性。規約：同じ指定値。使われ方：旧族の指定変換の保持。 -/
lemma indConeEndpointSliceFunctorIso_old : HEq
    ((indConeEndpointSliceFunctorIso V).precomp (joinInl T (Δ[0] : SSet.{u + 1})))
    (conePointSliceBoundaryFunctorIso (indConeEndpointPoint κ D)
      (joinMap (joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ≫ indConeEndpointBaseCone V)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp];
          exact indConeEndpointBaseCone_tip V)
      (joinMap (joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ≫ indConeEndpointSliceCone V)
      (by rw [Category.assoc]; rfl) (by
        rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
        exact indConeEndpointSliceCone_tip_uncurry V)) := by
  rw [indConeEndpointSliceFunctorIso_eq]
  exact conePointSliceBoundaryFunctorIso_precomp _ _ _ _ _ _ _
/-- 概要：同じ元の初期全円柱を保つ任意の再構成で、旧族での指定比較は変わらない。
方針：旧族の全余錐と全底を厳密に回収して同じ比較を照合。
規約：指定同型の値を保持。使われ方：指定変換を保持する再構成の選び直し。 -/
lemma indConeEndpointSliceFunctorIso_old_heq (V' : IndConeExtendedSliceData κ D q G)
    (hInitial : V.initial = V'.initial) : HEq
    ((indConeEndpointSliceFunctorIso V).precomp (joinInl T (Δ[0] : SSet.{u + 1})))
    ((indConeEndpointSliceFunctorIso V').precomp (joinInl T (Δ[0] : SSet.{u + 1}))) := by
  have hV := indConeEndpointSliceFunctorIso_old V
  have hV' := indConeEndpointSliceFunctorIso_old V'
  refine hV.trans (HEq.trans ?_ hV'.symm)
  apply conePointSliceBoundaryFunctorIso_heq
  · rw [indConeEndpointBaseCone_old, indConeEndpointBaseCone_old, hInitial]
  · rw [indConeEndpointSliceCone_old, indConeEndpointSliceCone_old, hInitial]
end SerrePositivity.InfinityCategories.F2.Ind
