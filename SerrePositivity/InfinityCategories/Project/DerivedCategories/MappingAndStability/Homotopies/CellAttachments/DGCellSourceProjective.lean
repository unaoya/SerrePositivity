module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.CellAttachments.DGCellAttachmentProjective
public import SerrePositivity.DifferentialGraded.Resolution.Cell

/-!
概要：固定した標準 cell source の全 Hom の K-projective 性。
方針：初期 cycle 被覆の自由 path、境界 cell 付加、分裂逐次余極限を順に使う。
規約：source・増大・cone の模型を変更しない。
使われ方：同じ source 上の固定 graph 解像度の各右制限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma complexUnit_isKProjective : (𝟙_ (Complex A)).IsKProjective := by
  apply isKProjective_of_homComplex_acyclic A
  intro N hN
  exact cochainAcyclic_of_iso hN (MonoidalClosed.unitIsoSelf (X := N)).symm

lemma dgCycleCoverHom_isKProjective (x y : D) :
    (homObject A (DGCategoryCycleCover.Source A D) x y).IsKProjective := by
  have hK (x y : D) : (DGCategoryCycleCover.edges A D x y).IsKProjective :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexCoproduct_isKProjective A _ (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSphere_isKProjective A j.1)
  have hw (w : List D) (x y : D) :
      (FreeDGCategory.wordTensor A D (DGCategoryCycleCover.edges A D) w x y).IsKProjective := by
    induction w generalizing x with
    | nil => exact hK x y
    | cons b w ih =>
      let := hK x b
      let := ih b
      exact complexTensor_isKProjective A _ _
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexCoproduct_isKProjective A
    (FreeDGCategory.pathTensor A D (DGCategoryCycleCover.edges A D))
  intro p
  cases p with
  | inl _ => exact complexUnit_isKProjective A
  | inr w => exact hw w x y

lemma dgCellStageHom_isKProjective (n : ℕ) (x y : D) :
    (DGCategoryCellResolution.stageHom A D n x y).IsKProjective := by
  induction n generalizing x y with
  | zero => exact dgCycleCoverHom_isKProjective A D x y
  | succ n ih =>
    exact @_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellAttachedHom_isKProjective A _ D
      (DGCategoryCellResolution.stage A D n).category _ _
      (DGCategoryCellResolution.stage A D n).cells
      (fun a b => ih a b) x y

lemma dgCellCandidateHom_isKProjective (x y : D) :
    (DGCategoryCellResolution.candidateHom A D x y).IsKProjective := by
  let F := DGCategoryCellResolution.homDiagram A D x y
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSequentialColimit_isKProjective A F (colimit.cocone F) (colimit.isColimit F)
    (fun n => dgCellStageHom_isKProjective A D n x y)
    (fun n i => @_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellOriginalGradedRetraction A _ D
      (DGCategoryCellResolution.stage A D n).category _
      (DGCategoryCellResolution.stage A D n).cellIndexSmall
      (DGCategoryCellResolution.stage A D n).cells x y i)
  intro n i
  change ((Functor.ofSequence (fun n => DGCategoryCellResolution.transition A D n x y)).map
    (homOfLE (Nat.le_succ n))).f i ≫ _ = _
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact @_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellOriginalGradedRetraction_fac A _ D
    (DGCategoryCellResolution.stage A D n).category _
    (DGCategoryCellResolution.stage A D n).cellIndexSmall
    (DGCategoryCellResolution.stage A D n).cells x y i

lemma dgCellSourceHom_isKProjective
    (x y : DGCategoryCellResolution.Source A D) :
    (homObject A (DGCategoryCellResolution.Source A D) x y).IsKProjective :=
  dgCellCandidateHom_isKProjective A D x.val y.val

end SerrePositivity.InfinityCategories.Project.DerivedCategories
