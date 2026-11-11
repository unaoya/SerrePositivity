module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace

/-!
概要：底を固定した形状制限は、相対内部 Hom の厳密な底変換。
方針：関手成分と共有する底射の普遍性を両側の引き戻しで照合する。
規約：底の充填性や形状の単射性は同定自体には不要。
使われ方：両端評価の相対持ち上げ性を元の定値底の path 模型へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：定値底の制限は元の相対内部 Hom の引き戻し。
方針：指定された全関手と制限の底射から、元の全空間へ一意に持ち上げる。
規約：全パラメータで厳密。使われ方：相対ホーンの持ち上げの底変換。 -/
lemma fiberwiseRestriction_isPullback {A K E B : SSet.{u}}
    (p : E ⟶ B) (i : A ⟶ K) (r : internalHom.PullbackObjObj i p) :
    IsPullback (pullback.fst ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p i) r.π (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseRestrictionBase p i r) := by
  have hc : pullback.fst ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) ≫ r.π =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p i ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseRestrictionBase p i r := by
    apply r.hom_ext
    · rw [Category.assoc, r.π_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseRestrictionBase_fst,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction_fst]
      rfl
    · rw [Category.assoc, r.π_snd, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseRestrictionBase_snd,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction_projection]
      exact pullback.condition
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hc)
  apply PullbackCone.isLimitAux'
  intro s
  have h₀ : s.fst ≫ (pre i).app E =
      s.snd ≫ pullback.fst ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram A B) := by
    have h := congrArg (fun z ↦ z ≫ r.fst) s.condition
    simp only [Category.assoc, r.π_fst, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseRestrictionBase_fst] at h
    change s.fst ≫ (pre i).app E =
      s.snd ≫ pullback.fst ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram A B) at h
    exact h
  have h₁ : s.fst ≫ (ihom K).map p =
      (s.snd ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B := by
    have h := congrArg (fun z ↦ z ≫ r.snd) s.condition
    simp only [Category.assoc, r.π_snd, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseRestrictionBase_snd] at h
    change s.fst ≫ (ihom K).map p =
      s.snd ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B at h
    exact h.trans (Category.assoc _ _ _).symm
  let a := pullback.lift s.fst (s.snd ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A) h₁
  refine ⟨a, ?_, ?_, ?_⟩
  · exact pullback.lift_fst _ _ _
  · change a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p i = s.snd
    apply pullback.hom_ext (f := (ihom A).map p) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram A B)
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction_fst, ← Category.assoc]
      rw [show a ≫ pullback.fst ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) = s.fst from
        pullback.lift_fst _ _ _]
      exact h₀
    · change (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p i) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A = _
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction_projection]
      exact pullback.lift_snd _ _ _
  · intro m hm ht
    apply pullback.hom_ext (f := (ihom K).map p) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B)
    · change m ≫ pullback.fst ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) =
        a ≫ pullback.fst ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B)
      rw [show a ≫ pullback.fst ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) = s.fst from
        pullback.lift_fst _ _ _]
      exact hm
    · change m ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p K = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p K
      have h := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A) ht
      change (m ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p i) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A = _ at h
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction_projection] at h
      exact h.trans (pullback.lift_snd _ _ _).symm

end SerrePositivity.InfinityCategories.Project.FilteredExchange
