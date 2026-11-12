module

public import SerrePositivity.KST.Spectra.PartialTotalizationMilnorKernel

/-!
概要：通常 Tot の Milnor 完全列の lim¹ からの単射と、実際の比較の核での完全性。
方針：構成済みの核の全単射の逆を核の包含へ合成し、基点・像・単射性を計算する。
規約：比較は実際の骨格への制限。lim¹ に群構造を要求しない。
使われ方：Goerss–Jardine VIII §1。通常 Tot の基点付き集合での Milnor 完全列。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.PartialTotalizationTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : CosimplicialObject PointedSimplicialSet.{u})
  (hX : reedyRight simplex J.rlp (terminal.from (X ⋙ PointedSimplicialSet.forget)))

/-- 通常 Tot の Milnor 完全列の lim¹ からの実際の単射。 -/
def limOneBoundary (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage X n).right (r + 1) (stage X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step X n)) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedTotalization.obj X).right r
        (PointedTotalization.obj X).basepoint := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  intro a
  exact ((kernelLimOneEquiv X hX r).symm a).val

/-- lim¹ の単射は標準基点を保つ。 -/
@[simp]
lemma limOneBoundary_point (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    limOneBoundary X hX r (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) = 1 := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  unfold limOneBoundary
  rw [kernelLimOneEquiv_symm_point]
  rfl

/-- 通常 Tot の lim¹ 項からの射は単射。 -/
lemma limOneBoundary_injective (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    Function.Injective (limOneBoundary X hX r) := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  exact Subtype.val_injective.comp (kernelLimOneEquiv X hX r).symm.injective

/-- 比較と lim¹ 項からの射の合成は単位元。 -/
@[simp]
lemma groupComparison_limOneBoundary (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    ∀ a : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stage X n).right (r + 1) (stage X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (step X n)),
      groupComparison X hX r (limOneBoundary X hX r a) = 1 := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  intro a
  exact ((kernelLimOneEquiv X hX r).symm a).property

/-- lim¹ 項の像は通常 Tot の実際の比較の核そのもの。 -/
lemma limOneBoundary_range (r : ℕ) :
    letI := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
    letI : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
    letI : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
    Set.range (limOneBoundary X hX r) = (groupComparison X hX r).ker := by
  let := PointedTotalization.kanComplex X ((CosimplicialHornFibration.terminal_iff _).mp hX)
  let : ∀ n, KanComplex (stage X n).right := fun n ↦ stage_kanComplex X hX n
  let : ∀ n, Fibration (step X n).right := fun n ↦ map_fibration X hX (Nat.le_succ n)
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact groupComparison_limOneBoundary X hX r a
  · intro hb
    refine ⟨kernelLimOneEquiv X hX r ⟨b, hb⟩, ?_⟩
    unfold limOneBoundary
    rw [Equiv.symm_apply_apply]

end
end SerrePositivity.KST.Spectra.PartialTotalizationTower
