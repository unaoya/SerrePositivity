module

public import SerrePositivity.KST.Spectra.PartialTotalizationLimit
public import SerrePositivity.KST.Spectra.TowerMilnorConvergence

/-!
概要：通常 Tot のホモトピー群と、部分 Tot 各段のホモトピー群の逆極限の比較。
方針：基点を保つ具体的な塔の極限同型を合成し、全射性と lim¹ 消滅の判定を移す。
規約：比較の各座標は構成済みの骨格への制限。係数の Reedy 条件だけを使う。
使われ方：Goerss–Jardine VIII §1。通常 Tot の塔の実際の収束比較。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet Opposite HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.PartialTotalizationTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : CosimplicialObject PointedSimplicialSet.{u})
  (hX : reedyRight simplex J.rlp (terminal.from (X ⋙ PointedSimplicialSet.forget)))

/-- 通常 Tot から骨格各段のホモトピー群の逆極限への実際の比較準同型。 -/
def groupComparison (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedTotalization.obj X).right r (PointedTotalization.obj X).basepoint →*
      PointedFibrationTower.compatibleGroup (stage X) (step X) r := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  exact (PointedFibrationTower.limitGroupComparison (stage X) (step X) r).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (limitIso X).hom (limitIso_basepoint X))

/-- 比較の各座標は通常 Tot から実際の骨格への制限。 -/
lemma groupComparison_apply (r n : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedTotalization.obj X).right r
      (PointedTotalization.obj X).basepoint,
    (groupComparison X hX r a).val n = pointedGroupMap r (restriction X n) a := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  intro a
  obtain ⟨s, rfl⟩ := Quotient.exists_rep a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map _ rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
  apply RelativeMorphism.ext
  change (s.map ≫ (limitIso X).hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ n =
    s.map ≫ (restriction X n).right
  rw [Category.assoc, limitIso_hom_projection]

/-- 通常 Tot の極限比較は、全正次数で全射。 -/
lemma groupComparison_surjective (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    Function.Surjective (groupComparison X hX r) := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  exact (PointedFibrationTower.limitGroupComparison_surjective (stage X) (step X) r).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r (limitIso X) (limitIso_basepoint X)).surjective

/-- 通常 Tot の極限比較が全単射であることは、次の群の塔の lim¹ 消滅と同値。 -/
lemma groupComparison_bijective_iff (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    Function.Bijective (groupComparison X hX r) ↔
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage X n).right (r + 1) (stage X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step X n))) := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r (limitIso X) (limitIso_basepoint X)
  constructor
  · intro h
    apply (PointedFibrationTower.limitGroupComparison_bijective_iff (stage X) (step X) r).1
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := e.surjective a
      obtain ⟨b', rfl⟩ := e.surjective b
      exact congrArg e (h.1 hab)
    · intro b
      obtain ⟨a, ha⟩ := h.2 b
      exact ⟨e a, ha⟩
  · intro h
    exact ((PointedFibrationTower.limitGroupComparison_bijective_iff
      (stage X) (step X) r).2 h).comp e.bijective

end
end SerrePositivity.KST.Spectra.PartialTotalizationTower
