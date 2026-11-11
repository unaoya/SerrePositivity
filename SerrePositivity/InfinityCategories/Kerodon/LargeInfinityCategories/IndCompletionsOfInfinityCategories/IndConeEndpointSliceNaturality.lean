module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndConeEndpointSliceOld
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConePointSliceBoundaryNaturality

/-!
概要：再構成した終点面の全余錐と底余錐を、元の旧族の同じ全余錐へ厳密に戻す。
方針：元の円柱全体を固定する等号を、同じ終点で制限する。
規約：元の旧族と下方余錐の入力を保持する。
使われ方：終点比較の旧族への制限が、拡張の選び方で変わらないことの確認。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (Δ[0] : SSet.{u})) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D}
  {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})))}
  (V : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndConeExtendedSliceData κ D q G)
/-- 概要：元の終点面の指定比較は、任意の元の点の同じ境界比較そのもの。
方針：元の定義を照合。規約：指定値の等号。使われ方：元の極大点評価の比較の制限。 -/
lemma indConeEndpointSliceFunctorIso_eq :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceFunctorIso V =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePointSliceBoundaryFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointPoint κ D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointBaseCone V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointBaseCone_tip V) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceCone V) rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceCone_tip_uncurry V) := rfl
/-- 概要：元の終点面の比較を旧族で制限すると、同じ制限余錐の指定比較を回収する。
方針：同じ点の元の比較の自然性。規約：同じ指定値。使われ方：旧族の指定変換の保持。 -/
lemma indConeEndpointSliceFunctorIso_old : HEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceFunctorIso V).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1})))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePointSliceBoundaryFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointPoint κ D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointBaseCone V)
      (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp];
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointBaseCone_tip V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceCone V)
      (by rw [Category.assoc]; rfl) (by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceCone_tip_uncurry V)) := by
  rw [indConeEndpointSliceFunctorIso_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePointSliceBoundaryFunctorIso_precomp _ _ _ _ _ _ _
/-- 概要：同じ元の初期全円柱を保つ任意の再構成で、旧族での指定比較は変わらない。
方針：旧族の全余錐と全底を厳密に回収して同じ比較を照合。
規約：指定同型の値を保持。使われ方：指定変換を保持する再構成の選び直し。 -/
lemma indConeEndpointSliceFunctorIso_old_heq (V' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndConeExtendedSliceData κ D q G)
    (hInitial : V.initial = V'.initial) : HEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceFunctorIso V).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1})))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceFunctorIso V').precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1}))) := by
  have hV := indConeEndpointSliceFunctorIso_old V
  have hV' := indConeEndpointSliceFunctorIso_old V'
  refine hV.trans (HEq.trans ?_ hV'.symm)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePointSliceBoundaryFunctorIso_heq
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointBaseCone_old, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointBaseCone_old, hInitial]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceCone_old, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeEndpointSliceCone_old, hInitial]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
