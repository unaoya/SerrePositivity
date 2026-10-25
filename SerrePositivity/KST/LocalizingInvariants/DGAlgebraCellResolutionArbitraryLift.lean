module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSuccessorCellMapLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellColimitDesc

/-!
概要：cell 源からの任意の代数射を全射擬同型に沿って厳密に持ち上げる。
方針：自由初期段から各後続 cell を延長し、元の余極限で貼り合わせる。
規約：元の増大射への持ち上げに限定せず、指定した射自身との合成を保つ。
使われ方：実乗法的単体模型の cell 源上のホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ k : ℤ, Function.Surjective (p.hom.f k)) (hq : QuasiIso p.hom)
  (f : cellResolution R A ⟶ B)

def liftedCellMapStages : ∀ n, {g : cellStage R A n ⟶ C //
    g ≫ p = cellStageInclusion R A n ≫ f}
  | 0 => ⟨initialCellMapLift R p hs hq (cellStageInclusion R A 0 ≫ f),
      initialCellMapLift_projection R p hs hq (cellStageInclusion R A 0 ≫ f)⟩
  | n + 1 =>
    let g := liftedCellMapStages n
    have hg : g.val ≫ p = cellStageTransition R A n ≫ (cellStageInclusion R A (n + 1) ≫ f) := by
      rw [← Category.assoc, cellStageTransition_inclusion]
      exact g.property
    ⟨successorCellMapLift R p hs hq n g.val (cellStageInclusion R A (n + 1) ≫ f) hg,
      successorCellMapLift_projection R p hs hq n g.val
        (cellStageInclusion R A (n + 1) ≫ f) hg⟩

lemma liftedCellMapStages_transition (n : ℕ) :
    cellStageTransition R A n ≫ (liftedCellMapStages R p hs hq f (n + 1)).val =
      (liftedCellMapStages R p hs hq f n).val :=
  successorCellMapLift_transition R p hs hq n (liftedCellMapStages R p hs hq f n).val
    (cellStageInclusion R A (n + 1) ≫ f) _

def cellResolutionArbitraryLift : cellResolution R A ⟶ C :=
  cellColimitDesc R (fun n => (liftedCellMapStages R p hs hq f n).val)
    (liftedCellMapStages_transition R p hs hq f)

lemma cellResolutionArbitraryLift_stage (n : ℕ) :
    cellStageInclusion R A n ≫ cellResolutionArbitraryLift R p hs hq f =
      (liftedCellMapStages R p hs hq f n).val :=
  cellColimitDesc_stage R _ _ n

lemma cellResolutionArbitraryLift_projection :
    cellResolutionArbitraryLift R p hs hq f ≫ p = f := by
  apply Mon.Hom.ext'
  apply colimit.hom_ext
  intro n
  change (cellStageInclusion R A n).hom ≫
      (cellColimitDescHom R (fun n => (liftedCellMapStages R p hs hq f n).val)
        (liftedCellMapStages_transition R p hs hq f) ≫ p.hom) =
    (cellStageInclusion R A n).hom ≫ f.hom
  rw [← Category.assoc, cellColimitDescHom_stage]
  exact congrArg Mon.Hom.hom (liftedCellMapStages R p hs hq f n).property

include hs hq in
lemma exists_cellResolutionArbitraryLift :
    ∃ g : cellResolution R A ⟶ C, g ≫ p = f :=
  ⟨cellResolutionArbitraryLift R p hs hq f, cellResolutionArbitraryLift_projection R p hs hq f⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
