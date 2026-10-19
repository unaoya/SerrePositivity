module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationPointHomFamily
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.F1.LeftFibrationTrivialComparison

/-!
概要：任意の点の全 Hom の族の同値性から、その点の始対象性を反映する。
方針：常に同値な Hom の持ち上げを消去し、終点評価の fiber ごとの同値性を全体へ移す。
規約：始対象性を仮定せず導出する。使われ方：共通 end での余錐族の同値性から余極限性を結論する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p] (d : E _⦋0⦌)

/-- 任意の点からの全 Hom の族が全ての終点で同値なら、その点は始対象。 -/
lemma isInitialVertex_of_pointHomFamily_equivalence
    (h : ∀ y : B _⦋0⦌, IsQCatEquivalence (leftFibrationPointHomFamily p d y)) :
    IsInitialVertex d := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm d)
  have : LeftFibration (q ≫ p) :=
    ⟨leftFibrations.comp_mem _ _ LeftFibration.mem LeftFibration.mem⟩
  have hq : IsQCatEquivalence q :=
    (leftFibration_isQCatEquivalence_iff_fibers (q ≫ p) p q rfl).mpr (by
      intro y
      have hL := (leftFibrationPointHomLift_homotopyEquivalence p d y).isQCatEquivalence
      exact hL.cancel_left (h y))
  exact (isInitialVertex_iff_trivialKanFibration d).mpr
    (trivialKanFibration_of_leftFibration_of_isQCatEquivalence q hq)

/-- 始対象性は、任意の点から作った全 Hom の族の実際のホモトピー同値性と同値。 -/
lemma isInitialVertex_iff_pointHomFamily_homotopyEquivalence :
    IsInitialVertex d ↔ ∀ y : B _⦋0⦌,
      IsSimplicialHomotopyEquivalence (leftFibrationPointHomFamily p d y) := by
  constructor
  · intro hd y
    exact leftFibrationPointHomFamily_homotopyEquivalence p d y hd
  · intro h
    apply isInitialVertex_of_pointHomFamily_equivalence p d
    intro y
    have : KanComplex (vertexFiber p y) := vertexFiber_kanComplex_of_leftFibration p y
    exact (h y).isQCatEquivalence

end
end SerrePositivity.InfinityCategories.HomotopyLimits
