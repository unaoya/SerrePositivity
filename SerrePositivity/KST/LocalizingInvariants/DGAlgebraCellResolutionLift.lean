module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSuccessorCellAlgebraLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellColimitDesc

/-!
概要：全射準同型を通る、cell 分解 augmentation の実代数的持ち上げ。
方針：自由初期段と後続 cell 延長を帰納し、互換な代数射を余極限で貼り合わせる。
規約：持ち上げの存在を仮定にしない。使われ方：導来平方零拡大の分類への準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)

def liftedCellStages : ∀ n, {g : cellStage R B n ⟶ C // g ≫ p = cellStageAugmentation R B n}
  | 0 => ⟨initialCellAlgebraLift R p hs hq, initialCellAlgebraLift_projection R p hs hq⟩
  | n + 1 =>
    let g := liftedCellStages n
    ⟨successorCellAlgebraLift R p hs hq n g.val g.property,
      successorCellAlgebraLift_projection R p hs hq n g.val g.property⟩

lemma liftedCellStages_transition (n : ℕ) :
    cellStageTransition R B n ≫ (liftedCellStages R p hs hq (n + 1)).val =
      (liftedCellStages R p hs hq n).val :=
  successorCellAlgebraLift_transition R p hs hq n
    (liftedCellStages R p hs hq n).val (liftedCellStages R p hs hq n).property

def cellResolutionLift : cellResolution R B ⟶ C :=
  cellColimitDesc R (fun n => (liftedCellStages R p hs hq n).val)
    (liftedCellStages_transition R p hs hq)

lemma cellResolutionLift_stage (n : ℕ) :
    cellStageInclusion R B n ≫ cellResolutionLift R p hs hq =
      (liftedCellStages R p hs hq n).val :=
  cellColimitDesc_stage R _ _ n

lemma cellResolutionLift_projection :
    cellResolutionLift R p hs hq ≫ p = cellAugmentation R B :=
  cellColimitDesc_projection R _ _ p (fun n => (liftedCellStages R p hs hq n).property)

lemma cellResolutionLift_quasiIso : QuasiIso (cellResolutionLift R p hs hq).hom := by
  have : QuasiIso p.hom := hq
  have : QuasiIso ((cellResolutionLift R p hs hq).hom ≫ p.hom) := by
    change QuasiIso ((cellResolutionLift R p hs hq ≫ p).hom)
    rw [cellResolutionLift_projection]
    exact cellAugmentation_quasiIso R B
  exact quasiIso_of_comp_right (cellResolutionLift R p hs hq).hom p.hom

include hs hq in
lemma exists_cellResolutionLift :
    ∃ g : cellResolution R B ⟶ C, g ≫ p = cellAugmentation R B :=
  ⟨cellResolutionLift R p hs hq, cellResolutionLift_projection R p hs hq⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
