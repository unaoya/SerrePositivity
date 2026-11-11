module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingTrivial

/-!
概要：三対象の span の比較の、pullback 上の全境界持ち上げ。
方針：中央の射を先に持ち上げ、左右の相対比較を同じ中央の持ち上げに沿って解く。
規約：三つの持ち上げは指定部分と両射影を厳密に保つ。
使われ方：局所化比較の立方体を、始点・終点の同時解像から構成する。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 三対象の span の可換比較が誘導する、実際の pullback の射。 -/
def spanPullbackMap {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀) :
    pullback p₁ p₂ ⟶ pullback q₁ q₂ :=
  pullback.lift (pullback.fst p₁ p₂ ≫ u₁) (pullback.snd p₁ p₂ ≫ u₂) (by
    rw [Category.assoc, h₁, ← Category.assoc, pullback.condition, Category.assoc, ← h₂,
      ← Category.assoc])

/-- span の比較の第一射影。 -/
lemma spanPullbackMap_fst {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀) :
    spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂ ≫ pullback.fst q₁ q₂ =
      pullback.fst p₁ p₂ ≫ u₁ := pullback.lift_fst _ _ _

/-- span の比較の第二射影。 -/
lemma spanPullbackMap_snd {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀) :
    spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂ ≫ pullback.snd q₁ q₂ =
      pullback.snd p₁ p₂ ≫ u₂ := pullback.lift_snd _ _ _

/-- 中央と左右の相対比較が全境界を持ち上げれば、span の pullback 比較も持ち上げる。 -/
lemma trivialKanFibration_spanPullbackMap_of_corners {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀)
    (c₁ : A₁ ⟶ pullback q₁ u₀) (c₂ : A₂ ⟶ pullback q₂ u₀)
    (hc₁f : c₁ ≫ pullback.fst q₁ u₀ = u₁) (hc₁s : c₁ ≫ pullback.snd q₁ u₀ = p₁)
    (hc₂f : c₂ ≫ pullback.fst q₂ u₀ = u₂) (hc₂s : c₂ ≫ pullback.snd q₂ u₀ = p₂)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration u₀] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration c₁] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration c₂] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂) := by
  constructor
  intro T U i hi
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := u₀) i hi
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := c₁) i hi
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := c₂) i hi
  constructor
  intro a b sq
  have ha : a ≫ pullback.fst p₁ p₂ ≫ u₁ = i ≫ b ≫ pullback.fst q₁ q₂ := by
    have he := congrArg (fun f ↦ f ≫ pullback.fst q₁ q₂) sq.w
    simpa only [Category.assoc, spanPullbackMap_fst] using he
  have hb : a ≫ pullback.snd p₁ p₂ ≫ u₂ = i ≫ b ≫ pullback.snd q₁ q₂ := by
    have he := congrArg (fun f ↦ f ≫ pullback.snd q₁ q₂) sq.w
    simpa only [Category.assoc, spanPullbackMap_snd] using he
  have s₀ : CommSq (a ≫ pullback.fst p₁ p₂ ≫ p₁) i u₀
      (b ≫ pullback.fst q₁ q₂ ≫ q₁) := by
    constructor
    simpa only [Category.assoc, h₁] using congrArg (fun f ↦ f ≫ q₁) ha
  let b₁ := pullback.lift (b ≫ pullback.fst q₁ q₂) s₀.lift s₀.fac_right.symm
  have hb₂ : (b ≫ pullback.snd q₁ q₂) ≫ q₂ = s₀.lift ≫ u₀ := by
    rw [s₀.fac_right, Category.assoc, pullback.condition]
  let b₂ := pullback.lift (b ≫ pullback.snd q₁ q₂) s₀.lift hb₂
  have s₁ : CommSq (a ≫ pullback.fst p₁ p₂) i c₁ b₁ := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, hc₁f, b₁, pullback.lift_fst]
      exact ha
    · simp only [Category.assoc, hc₁s, b₁, pullback.lift_snd]
      exact s₀.fac_left.symm
  have s₂ : CommSq (a ≫ pullback.snd p₁ p₂) i c₂ b₂ := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, hc₂f, b₂, pullback.lift_fst]
      exact hb
    · simp only [Category.assoc, hc₂s, b₂, pullback.lift_snd]
      rw [s₀.fac_left, pullback.condition]
  have hl₁ : s₁.lift ≫ p₁ = s₀.lift := by
    have he := congrArg (fun f ↦ f ≫ pullback.snd q₁ u₀) s₁.fac_right
    simpa only [Category.assoc, hc₁s, b₁, pullback.lift_snd] using he
  have hl₂ : s₂.lift ≫ p₂ = s₀.lift := by
    have he := congrArg (fun f ↦ f ≫ pullback.snd q₂ u₀) s₂.fac_right
    simpa only [Category.assoc, hc₂s, b₂, pullback.lift_snd] using he
  let L := pullback.lift s₁.lift s₂.lift (hl₁.trans hl₂.symm)
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply pullback.hom_ext
    · simp only [Category.assoc, L, pullback.lift_fst, s₁.fac_left]
    · simp only [Category.assoc, L, pullback.lift_snd, s₂.fac_left]
  · apply pullback.hom_ext
    · rw [Category.assoc, spanPullbackMap_fst, ← Category.assoc]
      rw [pullback.lift_fst]
      have he := congrArg (fun f ↦ f ≫ pullback.fst q₁ u₀) s₁.fac_right
      simpa only [Category.assoc, hc₁f, b₁, pullback.lift_fst] using he
    · rw [Category.assoc, spanPullbackMap_snd, ← Category.assoc]
      rw [pullback.lift_snd]
      have he := congrArg (fun f ↦ f ≫ pullback.fst q₂ u₀) s₂.fac_right
      simpa only [Category.assoc, hc₂f, b₂, pullback.lift_fst] using he

/-- 右成分と左の相対比較の持ち上げだけでも、span の pullback 比較を持ち上げられる。 -/
lemma trivialKanFibration_spanPullbackMap_of_left_corner {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀)
    (c₁ : A₁ ⟶ pullback q₁ u₀)
    (hc₁f : c₁ ≫ pullback.fst q₁ u₀ = u₁) (hc₁s : c₁ ≫ pullback.snd q₁ u₀ = p₁)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration u₂] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration c₁] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂) := by
  constructor
  intro T U i hi
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := u₂) i hi
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := c₁) i hi
  constructor
  intro a b sq
  have ha : a ≫ pullback.fst p₁ p₂ ≫ u₁ = i ≫ b ≫ pullback.fst q₁ q₂ := by
    have he := congrArg (fun f ↦ f ≫ pullback.fst q₁ q₂) sq.w
    simpa only [Category.assoc, spanPullbackMap_fst] using he
  have s₂ : CommSq (a ≫ pullback.snd p₁ p₂) i u₂ (b ≫ pullback.snd q₁ q₂) := by
    constructor
    have he := congrArg (fun f ↦ f ≫ pullback.snd q₁ q₂) sq.w
    simpa only [Category.assoc, spanPullbackMap_snd] using he
  have hw : (b ≫ pullback.fst q₁ q₂) ≫ q₁ = (s₂.lift ≫ p₂) ≫ u₀ := by
    calc
      (b ≫ pullback.fst q₁ q₂) ≫ q₁ = (b ≫ pullback.snd q₁ q₂) ≫ q₂ := by
        rw [Category.assoc, pullback.condition, Category.assoc]
      _ = (s₂.lift ≫ u₂) ≫ q₂ := congrArg (fun f ↦ f ≫ q₂) s₂.fac_right.symm
      _ = (s₂.lift ≫ p₂) ≫ u₀ := by rw [Category.assoc, h₂, Category.assoc]
  let b₁ := pullback.lift (b ≫ pullback.fst q₁ q₂) (s₂.lift ≫ p₂) hw
  have s₁ : CommSq (a ≫ pullback.fst p₁ p₂) i c₁ b₁ := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, hc₁f, b₁, pullback.lift_fst]
      exact ha
    · simp only [Category.assoc, hc₁s, b₁, pullback.lift_snd]
      rw [← Category.assoc i s₂.lift p₂, s₂.fac_left, Category.assoc, pullback.condition]
  have hl : s₁.lift ≫ p₁ = s₂.lift ≫ p₂ := by
    have he := congrArg (fun f ↦ f ≫ pullback.snd q₁ u₀) s₁.fac_right
    simpa only [Category.assoc, hc₁s, b₁, pullback.lift_snd] using he
  let L := pullback.lift s₁.lift s₂.lift hl
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply pullback.hom_ext
    · simp only [Category.assoc, L, pullback.lift_fst, s₁.fac_left]
    · simp only [Category.assoc, L, pullback.lift_snd, s₂.fac_left]
  · apply pullback.hom_ext
    · rw [Category.assoc, spanPullbackMap_fst, ← Category.assoc, pullback.lift_fst]
      have he := congrArg (fun f ↦ f ≫ pullback.fst q₁ u₀) s₁.fac_right
      simpa only [Category.assoc, hc₁f, b₁, pullback.lift_fst] using he
    · rw [Category.assoc, spanPullbackMap_snd, ← Category.assoc, pullback.lift_snd]
      exact s₂.fac_right

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
