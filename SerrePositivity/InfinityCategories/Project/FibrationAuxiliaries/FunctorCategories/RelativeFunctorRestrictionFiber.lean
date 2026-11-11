module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan

/-!
概要：相対内部 Hom の全境界持ち上げを、底を固定した相対関手の制限へ移す。
方針：境界の持ち上げを引き戻しの標的へ入れ、その解を同じ頂点 fiber へ戻す。
規約：左右の fibration 性を別に要求せず、指定した相対内部 Hom の自明 Kan 性だけを使う。
使われ方：left/right anodyne な制限と、表現可能前層の恒等点評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 相対内部 Hom の制限が自明 Kan なら、底を固定した相対関手の制限も自明 Kan。 -/
lemma relativeFunctorPre_trivialKanFibration_of_relativeHom {A D E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A)
    (sq' : internalHom.PullbackObjObj i p) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq'.π] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := sq'.π) (boundary n).ι inferInstance
  constructor
  intro u v sq
  let ιA := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  let ιD := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))
  let V : (Δ[n] : SSet.{u}) ⟶ sq'.pt :=
    sq'.isPullback.lift (v ≫ ιD) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) (by
      change (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))) ≫
        (ihom D).map p = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre i).app B
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
      rfl)
  have hVfst : V ≫ sq'.fst = v ≫ ιD := sq'.isPullback.lift_fst _ _ _
  have hVsnd : V ≫ sq'.snd = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := sq'.isPullback.lift_snd _ _ _
  have hs : CommSq (u ≫ ιA) (boundary n).ι sq'.π V := by
    constructor
    apply sq'.hom_ext
    · simp only [Category.assoc, sq'.π_fst, hVfst]
      change (u ≫ ιA) ≫ (pre i).app E = ((boundary n).ι ≫ v) ≫ ιD
      exact (congrArg (fun q ↦ q ≫ ιD) sq.w).trans (by rfl)
    · simp only [Category.assoc, sq'.π_snd, hVsnd]
      change (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) ≫ (ihom A).map p = _
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  have hbase : hs.lift ≫ (ihom A).map p = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := by
    calc
      _ = (hs.lift ≫ sq'.π) ≫ sq'.snd := by
        rw [Category.assoc]
        exact congrArg (fun q ↦ hs.lift ≫ q) sq'.π_snd.symm
      _ = V ≫ sq'.snd := congrArg (fun q ↦ q ≫ sq'.snd) hs.fac_right
      _ = _ := hVsnd
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) hs.lift hbase
  refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
    change ((boundary n).ι ≫ W) ≫ ιA = u ≫ ιA
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hs.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    change hs.lift ≫ (pre i).app E = v ≫ ιD
    calc
      _ = (hs.lift ≫ sq'.π) ≫ sq'.fst := by
        rw [Category.assoc]
        exact congrArg (fun q ↦ hs.lift ≫ q) sq'.π_fst.symm
      _ = V ≫ sq'.fst := congrArg (fun q ↦ q ≫ sq'.fst) hs.fac_right
      _ = _ := hVfst

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
