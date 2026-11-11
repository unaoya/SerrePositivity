module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.F1BFibrationsRightAnodyneTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalPointAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeApexTerminal

/-!
概要：right fibration で、指定始点と right anodyne な側面を同時に保つ円柱持ち上げ。
方針：二つの境界を pushout-product に貼り、その right anodyne 性で持ち上げる。
規約：底の全円柱を厳密に回収。使われ方：射図式の終点 comma の円柱族の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 任意の試験形状の右余錐の頂点包含は right anodyne。 -/
lemma conePoint_rightAnodyne (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u})) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.terminalPoint_rightAnodyne (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex_isTerminalVertex A)
  have he : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u}) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    have hp : (stdSimplex.obj₀Equiv.symm 0 : (Δ[0] : SSet.{u}) _⦋0⦌) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    exact congrArg (fun x => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) x) hp
  rwa [he] at h

/-- 指定始点・指定側面を持つ元の全円柱を、right fibration へ持ち上げる。 -/
lemma exists_rightFibration_prism_corner_lift {A D E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (j : D ⟶ A) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j)
    (b : A ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (a : A ⊗ (Δ[0] : SSet.{u}) ⟶ E) (d : D ⊗ (Δ[1] : SSet.{u}) ⟶ E)
    (h : (j ▷ (Δ[0] : SSet.{u})) ≫ a = (D ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1) ≫ d)
    (ha : a ≫ p = (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1) ≫ b)
    (hd : d ≫ p = (j ▷ (Δ[1] : SSet.{u})) ≫ b) :
    ∃ W : A ⊗ (Δ[1] : SSet.{u}) ⟶ E,
      W ≫ p = b ∧ (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1) ≫ W = a ∧
        (j ▷ (Δ[1] : SSet.{u})) ≫ W = d := by
  let sq := CategoryTheory.Functor.PushoutObjObj.ofHasPushout
    (curriedTensor SSet.{u}) j (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1)
  have hl : sq.inl ≫ sq.ι = A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 := sq.inl_ι
  have hr : sq.inr ≫ sq.ι = j ▷ (Δ[1] : SSet.{u}) := sq.inr_ι
  let t := sq.isPushout.desc a d h
  have ht : t ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.isPushout.inl_desc, ha,
        ← hl, Category.assoc]
    · rw [← Category.assoc, sq.isPushout.inr_desc, hd,
        ← hr, Category.assoc]
  have : HasLiftingProperty sq.ι p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightAnodyne_pushoutObjObj_left j hj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1) sq p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p))
  let L : CommSq t sq.ι p b := ⟨ht⟩
  refine ⟨L.lift, L.fac_right, ?_, ?_⟩
  · rw [← hl, Category.assoc, L.fac_left, sq.isPushout.inl_desc]
  · rw [← hr, Category.assoc, L.fac_left, sq.isPushout.inr_desc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
