module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialTower

/-!
概要：セル選択の包含に沿う、実部分 resolution の有限段の比較。
方針：前段の比較と自由層の包含から可換 square を作り、実 cone 関手で送る。
規約：比較の等式は元の有限段への単射で反映できる。
使われ方：D-8 d の κ-filtered strict 図式の関手性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) (s t : Set (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionLabel R D M))
  (hs : ∀ a ∈ s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDependencies R D M a ⊆ s)
  (ht : ∀ a ∈ t, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDependencies R D M a ⊆ t) (hst : s ⊆ t)

structure DGKappaPartialStageMap (n : ℕ) where
  map : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionObject R D M s hs n ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionObject R D M t ht n
  comm : map ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M t ht n).inclusion =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n).inclusion

def dgKappaPartialStageMapZero : DGKappaPartialStageMap R D M s t hs ht 0 where
  map := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleMap R D (moduleDiskCoverFamily R D M) (fun _ h => hst h)
  comm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleMap_inclusion R D _ _

variable {n : ℕ} (p : DGKappaPartialStageMap R D M s t hs ht n)

def dgKappaPartialKernelLayerMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModule R D (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModule R D (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M t n) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleMap R D _ (fun _ h => hst h)

lemma dgKappaPartialStageMap_square :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialAttachment R D M s hs
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n) ≫ p.map =
      dgKappaPartialKernelLayerMap R D M s t hst (n := n) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialAttachment R D M t ht
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M t ht n) := by
  let ps := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n
  let pt := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M t ht n
  let fs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialAttachment R D M s hs ps
  let ft := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialAttachment R D M t ht pt
  let us := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion R D
    (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n)
  let ut := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion R D
    (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M t n)
  let big := moduleKernelCellMap R D (moduleResolutionStage R D M n).hom
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaModuleMap_mono R D pt.inclusion pt.degreewiseMono
  apply (cancel_mono pt.inclusion).1
  have hp : p.map ≫ pt.inclusion = ps.inclusion := p.comm
  have hss : fs ≫ ps.inclusion = us ≫ big :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaKernelSubsetAttachment_square R D (moduleResolutionStage R D M n).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n) ps.inclusion ps.degreewiseMono
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialBoundaryLift R D M s hs ps)
  have htt : ft ≫ pt.inclusion = ut ≫ big :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaKernelSubsetAttachment_square R D (moduleResolutionStage R D M n).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M t n) pt.inclusion pt.degreewiseMono
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialBoundaryLift R D M t ht pt)
  change (fs ≫ p.map) ≫ pt.inclusion =
    (dgKappaPartialKernelLayerMap R D M s t hst ≫ ft) ≫ pt.inclusion
  rw [Category.assoc, hp, hss, Category.assoc, htt, ← Category.assoc]
  have hu : dgKappaPartialKernelLayerMap R D M s t hst (n := n) ≫ ut = us :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleMap_inclusion R D
      (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
      (s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n)
      (t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M t n) (fun _ h => hst h)
  exact congrArg (fun a => a ≫ big) hu.symm

def dgKappaPartialStageMapSucc : DGKappaPartialStageMap R D M s t hs ht (n + 1) where
  map := moduleConeMap R D _ _ (dgKappaPartialKernelLayerMap R D M s t hst) p.map
    (dgKappaPartialStageMap_square R D M s t hs ht hst p)
  comm := by
    let ps := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n
    let pt := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M t ht n
    let us := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion R D
      (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n)
    let ut := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion R D
      (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M t n)
    have hu : dgKappaPartialKernelLayerMap R D M s t hst (n := n) ≫ ut = us :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleMap_inclusion R D
        (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
        (s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n)
        (t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M t n) (fun _ h => hst h)
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaModuleConeMap_comp R D _ _ _
      (dgKappaPartialKernelLayerMap R D M s t hst) p.map ut pt.inclusion us ps.inclusion
      (dgKappaPartialStageMap_square R D M s t hs ht hst p)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaKernelSubsetAttachment_square R D (moduleResolutionStage R D M n).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M t n) pt.inclusion pt.degreewiseMono
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialBoundaryLift R D M t ht pt))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaKernelSubsetAttachment_square R D (moduleResolutionStage R D M n).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n) ps.inclusion ps.degreewiseMono
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialBoundaryLift R D M s hs ps)) hu p.comm

def dgKappaPartialStageMap : (n : ℕ) → DGKappaPartialStageMap R D M s t hs ht n
  | 0 => dgKappaPartialStageMapZero R D M s t hs ht hst
  | n + 1 => dgKappaPartialStageMapSucc R D M s t hs ht hst (dgKappaPartialStageMap n)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
