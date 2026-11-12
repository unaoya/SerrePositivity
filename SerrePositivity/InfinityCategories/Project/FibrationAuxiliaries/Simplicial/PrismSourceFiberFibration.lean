module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedPrismEndpointFibration

/-!
概要：二つの射の組の Kan fibration 性を第一成分の頂点 fiber に制限する。
方針：第一成分を定値にしたホーンを元の射で持ち上げる。
規約：始域と標的の Kan 性は要求しない。
使われ方：固定始点での終点評価の trivial Kan fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
  HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 概要：同時制限が Kan fibration なら第一成分の fiber 上の第二成分も Kan fibration。
方針：第一成分を定値にした同時のホーンを持ち上げ、fiber へ戻す。
規約：全ての単体集合と全ての頂点に適用できる。
使われ方：同時端点制限から固定始点の終点制限への移行。 -/
lemma fibration_sourceVertexFiber {S M N : SSet.{u}} (s : S ⟶ M) (t : S ⟶ N)
    [Fibration (lift s t)] (m : M _⦋0⦌) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι s m ≫ t) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn
  intro n k
  have := (SSet.modelCategoryQuillen.fibration_iff (lift s t)).mp inferInstance
    _ (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) k)
  constructor
  intro a b sq
  let c := lift (SSet.const m) b
  let sq' : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι s m) (horn (n + 1) k).ι (lift s t) c := ⟨by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, c]
    · simpa only [Category.assoc, c, lift_snd] using sq.w⟩
  have hs : sq'.lift ≫ s = SSet.const m := by
    have h := congrArg (fun w ↦ w ≫ fst M N) sq'.fac_right
    simpa only [Category.assoc, lift_fst, c] using h
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift s m sq'.lift hs
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext s m
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact sq'.fac_left
  · change (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι s m) ≫ t = b
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    have h := congrArg (fun w ↦ w ≫ snd M N) sq'.fac_right
    simpa only [Category.assoc, lift_snd, c] using h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
