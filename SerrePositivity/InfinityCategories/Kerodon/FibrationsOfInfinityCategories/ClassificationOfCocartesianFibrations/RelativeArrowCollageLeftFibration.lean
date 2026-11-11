module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeArrowCollageEndpointLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.IntervalCutDetection

/-!
概要：同じ底上の left fibration の間の任意の射を区間上の left fibration に実現する。
方針：時間の切断を零・全体・混合に分け端点と混合ホーンの持ち上げを合わせる。
規約：射自体の同値性や単射性は要求しない。
使われ方：非可逆な相対射を coherent な変換へ戻す主経路。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：任意の底上の射の区間実現は left fibration。
方針：定値の時間は両端の pullback、混合した時間は係数の充填と join の持ち上げを使う。
規約：底の quasicategory 性も射の可逆性も要求しない。
使われ方：一般の射の coherent な変換による表現。 -/
lemma relativeArrowCollageProjection_leftFibration {E F B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection f q) where
  mem := by
    intro A T j hj
    cases hj with
    | @intro n i hi =>
      constructor
      intro a b sq
      let t := b ≫ fst Δ[1] B
      let C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1
      by_cases hc0 : C = 0
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftHorn_hasLift_of_endpoint_pullback q _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 F)) 1
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollage_inr_isPullback f q) n i hi a b sq
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.intervalHom_eq_const_one_of_cut_zero t hc0)
      by_cases hcall : C = n + 2
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftHorn_hasLift_of_endpoint_pullback p _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f (𝟙 F)) 0
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollage_inl_isPullback p q f hf) n i hi a b sq
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.intervalHom_eq_const_zero_of_cut_all t hcall)
      have hbound : C ≤ n + 2 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _
      have hcpos : 0 < C := by omega
      have hcmix : C ≤ n + 1 := by omega
      cases n with
      | zero =>
        have hi0 : i = 0 := by
          apply Fin.ext
          change i.val < 1 at hi
          change i.val = 0
          omega
        subst i
        have ht : t = 𝟙 Δ[1] := by
          apply SSet.yonedaEquiv.injective
          apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.intervalSimplex_eq_of_pullCut_eq
          change C = _
          have hc : C = 1 := by omega
          rw [hc]
          decide
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollage_crossing_edge_hasLift p q f hf a b sq ht
      | succ n =>
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollage_mixed_leftHorn_hasLift f q n i hi a b sq hcpos hcmix

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
