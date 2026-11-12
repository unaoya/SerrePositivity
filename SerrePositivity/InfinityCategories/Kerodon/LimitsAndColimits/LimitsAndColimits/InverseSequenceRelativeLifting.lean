module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.DiscreteLimitComparison
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：可算 inverse diagram の相対 corner の持ち上げを、極限の比較へ移す。
方針：指定部分と標的の像を保つ lift を初段から逐次構成し、極限錐へまとめる。
規約：各成分の持ち上げだけでなく相対 corner の持ち上げを用いる。
使われ方：可逆 path の同時解像による、可算骨格の局所化比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet Opposite
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 可算 inverse diagram の比較の、一段前の lift を固定する相対 corner。 -/
def inverseSequenceCorner {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) (n : ℕ) :
    F.obj (op (n + 1)) ⟶ pullback (G.map (homOfLE (Nat.le_succ n)).op) (η.app (op n)) :=
  pullback.lift (η.app (op (n + 1))) (F.map (homOfLE (Nat.le_succ n)).op)
    (η.naturality (homOfLE (Nat.le_succ n)).op).symm

/-- 相対 corner の第一射影は元の比較の次段の成分。 -/
lemma inverseSequenceCorner_fst {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) (n : ℕ) :
    inverseSequenceCorner η n ≫
        pullback.fst (G.map (homOfLE (Nat.le_succ n)).op) (η.app (op n)) =
      η.app (op (n + 1)) := pullback.lift_fst _ _ _

/-- 相対 corner の第二射影は始域図式の遷移。 -/
lemma inverseSequenceCorner_snd {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) (n : ℕ) :
    inverseSequenceCorner η n ≫
        pullback.snd (G.map (homOfLE (Nat.le_succ n)).op) (η.app (op n)) =
      F.map (homOfLE (Nat.le_succ n)).op := pullback.lift_snd _ _ _

section Stages
variable {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) (c : Cone F) (d : Cone G)
  (u : c.pt ⟶ d.pt) (hu : ∀ j, u ≫ d.π.app j = c.π.app j ≫ η.app j)
  {U V : SSet.{u}} (i : U ⟶ V) [HasLiftingProperty i (η.app (op 0))]
  [∀ n, HasLiftingProperty i (inverseSequenceCorner η n)]
  (a : U ⟶ c.pt) (b : V ⟶ d.pt) (sq : CommSq a i u b)

include hu sq

omit [HasLiftingProperty i (η.app (op 0))]
  [∀ n, HasLiftingProperty i (inverseSequenceCorner η n)] in
/-- 各段の持ち上げ問題は、元の極限の比較の持ち上げ問題から得られる。 -/
lemma inverseSequenceStage_comm (n : ℕ) :
    (a ≫ c.π.app (op n)) ≫ η.app (op n) = i ≫ (b ≫ d.π.app (op n)) := by
  rw [Category.assoc, ← hu, ← Category.assoc, sq.w, Category.assoc]

/-- 指定部分と標的の像を固定した各段の lift を、相対 corner により逐次構成する。 -/
def inverseSequenceLiftStages : ∀ n,
    { l : V ⟶ F.obj (op n) // i ≫ l = a ≫ c.π.app (op n) ∧
      l ≫ η.app (op n) = b ≫ d.π.app (op n) }
  | 0 =>
    let s : CommSq (a ≫ c.π.app (op 0)) i (η.app (op 0)) (b ≫ d.π.app (op 0)) :=
      ⟨inverseSequenceStage_comm η c d u hu i a b sq 0⟩
    ⟨s.lift, s.fac_left, s.fac_right⟩
  | n + 1 =>
    let prev := inverseSequenceLiftStages n
    let B := pullback.lift (b ≫ d.π.app (op (n + 1))) prev.val (by
      rw [Category.assoc, d.w, prev.property.2])
    let s : CommSq (a ≫ c.π.app (op (n + 1))) i (inverseSequenceCorner η n) B := by
      constructor
      apply pullback.hom_ext
      · simp only [Category.assoc, inverseSequenceCorner_fst, B, pullback.lift_fst]
        simpa only [Category.assoc] using
          inverseSequenceStage_comm η c d u hu i a b sq (n + 1)
      · simp only [Category.assoc, inverseSequenceCorner_snd, B, pullback.lift_snd,
          c.w, prev.property.1]
    ⟨s.lift, s.fac_left, by
      have he := congrArg (fun f ↦ f ≫
        pullback.fst (G.map (homOfLE (Nat.le_succ n)).op) (η.app (op n))) s.fac_right
      simpa only [Category.assoc, inverseSequenceCorner_fst, B, pullback.lift_fst] using he⟩

/-- 逐次構成した lift は、隣接する段の遷移を厳密に保つ。 -/
lemma inverseSequenceLiftStages_comp (n : ℕ) :
    (inverseSequenceLiftStages η c d u hu i a b sq (n + 1)).val ≫
        F.map (homOfLE (Nat.le_succ n)).op =
      (inverseSequenceLiftStages η c d u hu i a b sq n).val := by
  dsimp only [inverseSequenceLiftStages]
  rw [← inverseSequenceCorner_snd η n, ← Category.assoc, CommSq.fac_right,
    pullback.lift_snd]
end Stages

/-- 初段と全ての相対 corner の右持ち上げは、極限の比較の右持ち上げを与える。 -/
lemma hasLiftingProperty_inverseSequenceConeMap {F G : ℕᵒᵖ ⥤ SSet.{u}}
    (η : F ⟶ G) (c : Cone F) (d : Cone G) (hc : IsLimit c) (hd : IsLimit d)
    (u : c.pt ⟶ d.pt) (hu : ∀ j, u ≫ d.π.app j = c.π.app j ≫ η.app j)
    {U V : SSet.{u}} (i : U ⟶ V) [HasLiftingProperty i (η.app (op 0))]
    [∀ n, HasLiftingProperty i (inverseSequenceCorner η n)] : HasLiftingProperty i u := by
  constructor
  intro a b sq
  let L := inverseSequenceLiftStages η c d u hu i a b sq
  let s : Cone F := {
    pt := V
    π := NatTrans.ofOpSequence (fun n ↦ (L n).val) (fun n ↦ by
      change 𝟙 V ≫ (L n).val = (L (n + 1)).val ≫ F.map (homOfLE (Nat.le_succ n)).op
      rw [Category.id_comp]
      exact (inverseSequenceLiftStages_comp η c d u hu i a b sq n).symm) }
  refine CommSq.HasLift.mk' { l := hc.lift s, fac_left := ?_, fac_right := ?_ }
  · apply hc.hom_ext
    intro j
    rw [Category.assoc, hc.fac]
    exact (L j.unop).property.1
  · apply hd.hom_ext
    intro j
    rw [Category.assoc, hu, ← Category.assoc, hc.fac]
    exact (L j.unop).property.2

/-- 初段と相対 corner が全境界を持ち上げる塔の比較は、極限でも全境界を持ち上げる。 -/
lemma trivialKanFibration_inverseSequenceConeMap {F G : ℕᵒᵖ ⥤ SSet.{u}}
    (η : F ⟶ G) (c : Cone F) (d : Cone G) (hc : IsLimit c) (hd : IsLimit d)
    (u : c.pt ⟶ d.pt) (hu : ∀ j, u ≫ d.π.app j = c.π.app j ≫ η.app j)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (η.app (op 0))]
    [∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (inverseSequenceCorner η n)] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration u := by
  constructor
  intro U V i hi
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := η.app (op 0)) i hi
  have : ∀ n, HasLiftingProperty i (inverseSequenceCorner η n) := fun n ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := inverseSequenceCorner η n) i hi
  exact hasLiftingProperty_inverseSequenceConeMap η c d hc hd u hu i

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
