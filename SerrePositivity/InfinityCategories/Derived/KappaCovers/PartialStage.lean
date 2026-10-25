module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.CellAttachment
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.ResolutionDependencies

/-!
概要：依存閉なセル選択に対する、小さい実 cell resolution の有限段。
方針：選択した disk から始め、境界を単射で反映して kernel cell の cone を取る。
規約：この有限段構成では κ の濃度仮定を使わない。
使われ方：D-8 d の依存閉部分集合に沿う可算 cell 列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded CochainComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) (s : Set (DGKappaResolutionLabel R D M))

structure DGKappaResolutionPartialStage (n : ℕ) where
  object : ModuleCategory R D
  inclusion : object ⟶ (moduleResolutionStage R D M n).left
  degreewiseMono : ∀ x q, Mono (((moduleEvaluation R D x).map inclusion).f q)
  supported : ∀ x q z, DGKappaResolutionElementSupported R D M s n x q z →
    ∃ a, ((moduleEvaluation R D x).map inclusion).f q a = z

def dgKappaResolutionPartialStageZero : DGKappaResolutionPartialStage R D M s 0 where
  object := dgKappaSubsetModule R D (moduleDiskCoverFamily R D M)
    (dgKappaResolutionDiskSelection R D M s)
  inclusion := dgKappaSubsetModuleInclusion R D (moduleDiskCoverFamily R D M)
    (dgKappaResolutionDiskSelection R D M s)
  degreewiseMono := dgKappaSubsetModuleInclusion_degreewiseMono R D _ _
  supported _ _ _ h := h

variable (hs : ∀ a ∈ s, dgKappaResolutionDependencies R D M a ⊆ s)
  {n : ℕ} (p : DGKappaResolutionPartialStage R D M s n)

def dgKappaResolutionPartialBoundaryLift
    (j : dgKappaResolutionKernelSelection R D M s n) :
    ∃ a, ((moduleEvaluation R D j.val.1).map p.inclusion).f (j.val.2.1 + 1) a =
      j.val.2.2.val.val :=
  p.supported _ _ _ (dgKappaResolutionKernel_supported R D M s hs n j)

def dgKappaResolutionPartialAttachment :
    dgKappaSubsetModule R D
      (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
      (dgKappaResolutionKernelSelection R D M s n) ⟶ p.object :=
  dgKappaKernelSubsetAttachment R D (moduleResolutionStage R D M n).hom
    (dgKappaResolutionKernelSelection R D M s n) p.inclusion p.degreewiseMono
    (dgKappaResolutionPartialBoundaryLift R D M s hs p)

def dgKappaResolutionPartialStageSucc : DGKappaResolutionPartialStage R D M s (n + 1) where
  object := moduleCone R D (dgKappaResolutionPartialAttachment R D M s hs p)
  inclusion := dgKappaKernelSubsetStepInclusion R D (moduleResolutionStage R D M n).hom
    (dgKappaResolutionKernelSelection R D M s n) p.inclusion p.degreewiseMono
    (dgKappaResolutionPartialBoundaryLift R D M s hs p)
  degreewiseMono := dgKappaKernelSubsetStepInclusion_degreewiseMono R D _ _ _ _ _
  supported x q z hz := by
    obtain ⟨a, b, ha, he⟩ := hz
    obtain ⟨a', ha'⟩ := p.supported x q a ha
    let f := (moduleEvaluation R D x).map (dgKappaResolutionPartialAttachment R D M s hs p)
    refine ⟨(mappingCone.inr f).f q a' + (mappingCone.inl f).v (q + 1) q (by omega) b, ?_⟩
    change ((moduleEvaluation R D x).map (moduleConeMap R D _ _ _ _ _)).f q _ = z
    rw [moduleConeMap_eval]
    refine (dgKappaConeMap_element _ _ _ _ _ q b a').trans ?_
    simpa only [ha'] using! he

def dgKappaResolutionPartialStage : (n : ℕ) → DGKappaResolutionPartialStage R D M s n
  | 0 => dgKappaResolutionPartialStageZero R D M s
  | n + 1 => dgKappaResolutionPartialStageSucc R D M s hs
    (dgKappaResolutionPartialStage n)

end SerrePositivity.InfinityCategories
