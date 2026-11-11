module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct

/-!
概要：相対内部 Hom の持ち上げ性を固定した図式の相対関手空間へ移す。
方針：底を定値の図式に固定した比較を作り、持ち上げを後合成の fiber へ戻す。
規約：持ち上げる射 j は任意で、ホーンや境界への制限は要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手空間の制限の充填性の共通部分。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：相対内部 Hom の比較射の持ち上げ性は相対関手の前合成にも成り立つ。
方針：下の図式に定値の A 上の底の図式を添え、持ち上げの底が固定されることを確認する。
規約：p、i、j の充填性や単射性は個別には要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手の制限のホーン・境界の統一した判定。 -/
lemma hasLiftingProperty_relativeFunctorPre {A D E B T U : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A)
    (r : internalHom.PullbackObjObj i p) (j : T ⟶ U) [HasLiftingProperty j r.π] :
    HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) := by
  constructor
  intro u v sq
  let ιA := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  let ιD := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))
  let V : U ⟶ r.pt := r.isPullback.lift (v ≫ ιD) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) (by
    change (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))) ≫
      (ihom D).map p = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre i).app B
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
    rfl)
  have hVfst : V ≫ r.fst = v ≫ ιD := r.isPullback.lift_fst _ _ _
  have hVsnd : V ≫ r.snd = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := r.isPullback.lift_snd _ _ _
  have hs : CommSq (u ≫ ιA) j r.π V := by
    constructor
    apply r.hom_ext
    · simp only [Category.assoc, r.π_fst, hVfst]
      change (u ≫ ιA) ≫ (pre i).app E = (j ≫ v) ≫ ιD
      exact (congrArg (fun q ↦ q ≫ ιD) sq.w).trans (by rfl)
    · simp only [Category.assoc, r.π_snd, hVsnd]
      change (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) ≫ (ihom A).map p = _
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  have hbase : hs.lift ≫ (ihom A).map p = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := by
    calc
      _ = (hs.lift ≫ r.π) ≫ r.snd := by
        rw [Category.assoc]
        exact congrArg (fun q ↦ hs.lift ≫ q) r.π_snd.symm
      _ = V ≫ r.snd := congrArg (fun q ↦ q ≫ r.snd) hs.fac_right
      _ = _ := hVsnd
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) hs.lift hbase
  refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
    change (j ≫ W) ≫ ιA = u ≫ ιA
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hs.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    change hs.lift ≫ (pre i).app E = v ≫ ιD
    calc
      _ = (hs.lift ≫ r.π) ≫ r.fst := by
        rw [Category.assoc]
        exact congrArg (fun q ↦ hs.lift ≫ q) r.π_fst.symm
      _ = V ≫ r.fst := congrArg (fun q ↦ q ≫ r.fst) hs.fac_right
      _ = _ := hVfst

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
