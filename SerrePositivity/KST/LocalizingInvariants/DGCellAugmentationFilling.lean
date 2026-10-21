module

public import SerrePositivity.KST.LocalizingInvariants.CochainBoundaryFillingEpi
public import SerrePositivity.DifferentialGraded.Resolution.CellCategory

/-!
概要：既存固定対象 cell 分解の増大射が、全境界 cell を実際に充填することを示す。
方針：指定 cycle の有限段階表示と次段の cell 充填を、元の逐次余極限へ渡す。
規約：D の実構成を読み取り専用で使用。使われ方：一対象 dg 代数分解の全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
open DGCategoryCellResolution

lemma dgCellAugmentation_fills (x y : D)
    (c : ComplexBoundaryCell R (candidateAugmentation R D x y)) : c.HasFilling R := by
  apply ComplexBoundaryCell.sequential_filling R (homDiagram R D x y)
    (colimit.cocone _) (augmentationCocone R D x y) (colimit.isColimit _)
    (fun n d ↦ ?_) c
  change ComplexBoundaryCell R (stageAugmentation R D n x y) at d
  change ∃ t : (stageHom R D (n + 1) x y).X d.degree,
    (stageHom R D (n + 1) x y).d d.degree (d.degree + 1) t =
      ((homDiagram R D x y).map (homOfLE (Nat.le_succ n))).f (d.degree + 1) d.cycle.val ∧
    (stageAugmentation R D (n + 1) x y).f d.degree t = d.primitive
  dsimp only [homDiagram]
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact stage_fills R D n x y d

lemma dgCellAugmentation_component_epi (x y : D) (n : ℤ) :
    Epi ((candidateAugmentation R D x y).f n) :=
  cochain_component_epi_of_boundaryFilling _ (dgCellAugmentation_fills R D x y) n

end SerrePositivity.KST.LocalizingInvariants
